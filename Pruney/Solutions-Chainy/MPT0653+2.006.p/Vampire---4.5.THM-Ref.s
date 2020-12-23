%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:59 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 560 expanded)
%              Number of leaves         :   32 ( 230 expanded)
%              Depth                    :   21
%              Number of atoms          : 1328 (4043 expanded)
%              Number of equality atoms :  350 (1473 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f588,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f113,f142,f163,f176,f186,f234,f248,f265,f288,f307,f316,f402,f421,f452,f456,f503,f521,f564,f569,f579,f586,f587])).

fof(f587,plain,
    ( sK3(sK0,sK1) != k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1))
    | sK2(sK0,sK1) != k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f586,plain,
    ( ~ spl5_27
    | ~ spl5_28
    | spl5_29
    | ~ spl5_50 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | ~ spl5_27
    | ~ spl5_28
    | spl5_29
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f584,f519])).

fof(f519,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f518])).

fof(f518,plain,
    ( spl5_50
  <=> r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f584,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ spl5_27
    | ~ spl5_28
    | spl5_29 ),
    inference(subsumption_resolution,[],[f571,f314])).

fof(f314,plain,
    ( sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | spl5_29 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl5_29
  <=> sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f571,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ spl5_27
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f317,f306])).

fof(f306,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl5_28
  <=> r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f317,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ spl5_27 ),
    inference(superposition,[],[f64,f302])).

fof(f302,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl5_27
  <=> sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f64,plain,(
    ! [X2] :
      ( ~ r2_hidden(k1_funct_1(sK0,X2),k1_relat_1(sK1))
      | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2
      | ~ r2_hidden(X2,k1_relat_1(sK0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,X3) = X2
      | k1_funct_1(sK0,X2) != X3
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k2_funct_1(sK0) != sK1
    & ! [X2,X3] :
        ( ( ( k1_funct_1(sK0,X2) = X3
            | k1_funct_1(sK1,X3) != X2 )
          & ( k1_funct_1(sK1,X3) = X2
            | k1_funct_1(sK0,X2) != X3 ) )
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK0)) )
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & k1_relat_1(sK0) = k2_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & ! [X2,X3] :
                ( ( ( k1_funct_1(X0,X2) = X3
                    | k1_funct_1(X1,X3) != X2 )
                  & ( k1_funct_1(X1,X3) = X2
                    | k1_funct_1(X0,X2) != X3 ) )
                | ~ r2_hidden(X3,k1_relat_1(X1))
                | ~ r2_hidden(X2,k1_relat_1(X0)) )
            & k1_relat_1(X1) = k2_relat_1(X0)
            & k1_relat_1(X0) = k2_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & ! [X3,X2] :
              ( ( ( k1_funct_1(sK0,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(sK0,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(sK0)) )
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & k2_relat_1(X1) = k1_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & ! [X3,X2] :
            ( ( ( k1_funct_1(sK0,X2) = X3
                | k1_funct_1(X1,X3) != X2 )
              & ( k1_funct_1(X1,X3) = X2
                | k1_funct_1(sK0,X2) != X3 ) )
            | ~ r2_hidden(X3,k1_relat_1(X1))
            | ~ r2_hidden(X2,k1_relat_1(sK0)) )
        & k1_relat_1(X1) = k2_relat_1(sK0)
        & k2_relat_1(X1) = k1_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & ! [X3,X2] :
          ( ( ( k1_funct_1(sK0,X2) = X3
              | k1_funct_1(sK1,X3) != X2 )
            & ( k1_funct_1(sK1,X3) = X2
              | k1_funct_1(sK0,X2) != X3 ) )
          | ~ r2_hidden(X3,k1_relat_1(sK1))
          | ~ r2_hidden(X2,k1_relat_1(sK0)) )
      & k2_relat_1(sK0) = k1_relat_1(sK1)
      & k1_relat_1(sK0) = k2_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( ( k1_funct_1(X0,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(X0,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2,X3] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X2,k1_relat_1(X0)) )
                   => ( k1_funct_1(X0,X2) = X3
                    <=> k1_funct_1(X1,X3) = X2 ) )
                & k1_relat_1(X1) = k2_relat_1(X0)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2,X3] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X2,k1_relat_1(X0)) )
                 => ( k1_funct_1(X0,X2) = X3
                  <=> k1_funct_1(X1,X3) = X2 ) )
              & k1_relat_1(X1) = k2_relat_1(X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).

fof(f579,plain,
    ( spl5_50
    | ~ spl5_49
    | ~ spl5_55 ),
    inference(avatar_split_clause,[],[f575,f561,f500,f518])).

fof(f500,plain,
    ( spl5_49
  <=> sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f561,plain,
    ( spl5_55
  <=> r2_hidden(k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f575,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ spl5_49
    | ~ spl5_55 ),
    inference(backward_demodulation,[],[f562,f502])).

fof(f502,plain,
    ( sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f500])).

fof(f562,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl5_55 ),
    inference(avatar_component_clause,[],[f561])).

fof(f569,plain,
    ( ~ spl5_14
    | ~ spl5_28
    | spl5_55 ),
    inference(avatar_contradiction_clause,[],[f568])).

fof(f568,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_28
    | spl5_55 ),
    inference(subsumption_resolution,[],[f566,f306])).

fof(f566,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ spl5_14
    | spl5_55 ),
    inference(resolution,[],[f563,f175])).

fof(f175,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK0),X0),k1_relat_1(sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl5_14
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(k2_funct_1(sK0),X0),k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f563,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)),k1_relat_1(sK0))
    | spl5_55 ),
    inference(avatar_component_clause,[],[f561])).

fof(f564,plain,
    ( ~ spl5_55
    | spl5_49
    | ~ spl5_28
    | ~ spl5_29
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f557,f449,f313,f304,f500,f561])).

fof(f449,plain,
    ( spl5_43
  <=> sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f557,plain,
    ( sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1))
    | ~ r2_hidden(k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl5_28
    | ~ spl5_29
    | ~ spl5_43 ),
    inference(forward_demodulation,[],[f458,f315])).

fof(f315,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f313])).

fof(f458,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1))
    | ~ r2_hidden(k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl5_28
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f457,f306])).

fof(f457,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | k1_funct_1(sK1,sK2(sK0,sK1)) = k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1))
    | ~ r2_hidden(k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl5_43 ),
    inference(superposition,[],[f64,f451])).

fof(f451,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f449])).

fof(f521,plain,
    ( ~ spl5_50
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8
    | ~ spl5_27
    | ~ spl5_28
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f516,f313,f304,f300,f110,f100,f95,f90,f85,f80,f75,f518])).

fof(f75,plain,
    ( spl5_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f80,plain,
    ( spl5_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f85,plain,
    ( spl5_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f90,plain,
    ( spl5_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f95,plain,
    ( spl5_5
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f100,plain,
    ( spl5_6
  <=> k2_funct_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f110,plain,
    ( spl5_8
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f516,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8
    | ~ spl5_27
    | ~ spl5_28
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f515,f306])).

fof(f515,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f514,f112])).

fof(f112,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f514,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f513,f77])).

fof(f77,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f513,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f512,f82])).

fof(f82,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f512,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f511,f97])).

fof(f97,plain,
    ( v2_funct_1(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f511,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f510,f87])).

fof(f87,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f510,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f509,f92])).

fof(f92,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f509,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl5_6
    | ~ spl5_8
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f508,f112])).

fof(f508,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl5_6
    | ~ spl5_27
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f507,f302])).

fof(f507,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl5_6
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f506,f102])).

fof(f102,plain,
    ( k2_funct_1(sK0) != sK1
    | spl5_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f506,plain,
    ( k2_funct_1(sK0) = sK1
    | ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_29 ),
    inference(trivial_inequality_removal,[],[f504])).

fof(f504,plain,
    ( sK3(sK0,sK1) != sK3(sK0,sK1)
    | k2_funct_1(sK0) = sK1
    | ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_29 ),
    inference(superposition,[],[f58,f315])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k2_funct_1(X0) = X1
      | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0))
      | sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
      | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
                  | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
                & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
              | ( ( sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
                  | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
                & r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ( ( k1_funct_1(X0,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & k1_funct_1(X1,X2) = X3
            & r2_hidden(X2,k2_relat_1(X0)) ) )
     => ( ( ( sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
          & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
          & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
        | ( ( sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
            | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
          & r2_hidden(sK2(X0,X1),k2_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

fof(f503,plain,
    ( spl5_29
    | spl5_49
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_27
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f464,f454,f300,f100,f90,f85,f500,f313])).

fof(f454,plain,
    ( spl5_44
  <=> ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0
        | sK3(sK0,X0) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f464,plain,
    ( sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_27
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f463,f302])).

fof(f463,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,sK1)))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f462,f102])).

fof(f462,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | k2_funct_1(sK0) = sK1
    | sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,sK1)))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f461,f87])).

fof(f461,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK0) = sK1
    | sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,sK1)))
    | ~ spl5_4
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f460,f92])).

fof(f460,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK0) = sK1
    | sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,sK1)))
    | ~ spl5_44 ),
    inference(equality_resolution,[],[f455])).

fof(f455,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0
        | sK3(sK0,X0) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,X0))) )
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f454])).

fof(f456,plain,
    ( spl5_44
    | ~ spl5_15
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f272,f246,f184,f454])).

fof(f184,plain,
    ( spl5_15
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f246,plain,
    ( spl5_21
  <=> ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f272,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0
        | sK3(sK0,X0) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,X0))) )
    | ~ spl5_15
    | ~ spl5_21 ),
    inference(resolution,[],[f247,f185])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0 )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f184])).

fof(f247,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | k1_relat_1(X0) != k1_relat_1(sK1)
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f246])).

fof(f452,plain,
    ( spl5_43
    | ~ spl5_11
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f425,f304,f140,f449])).

fof(f140,plain,
    ( spl5_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f425,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)))
    | ~ spl5_11
    | ~ spl5_28 ),
    inference(resolution,[],[f306,f141])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),X0)) = X0 )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f421,plain,
    ( spl5_28
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_27
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f420,f400,f300,f100,f90,f85,f304])).

fof(f400,plain,
    ( spl5_40
  <=> ! [X1] :
        ( r2_hidden(sK2(sK0,X1),k1_relat_1(sK1))
        | k1_relat_1(X1) != k1_relat_1(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k2_funct_1(sK0) = X1
        | r2_hidden(k1_funct_1(sK0,sK3(sK0,X1)),k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f420,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_27
    | ~ spl5_40 ),
    inference(duplicate_literal_removal,[],[f419])).

fof(f419,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_27
    | ~ spl5_40 ),
    inference(forward_demodulation,[],[f418,f302])).

fof(f418,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k1_relat_1(sK1))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f417,f102])).

fof(f417,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | k2_funct_1(sK0) = sK1
    | r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k1_relat_1(sK1))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f416,f87])).

fof(f416,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK0) = sK1
    | r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k1_relat_1(sK1))
    | ~ spl5_4
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f408,f92])).

fof(f408,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK0) = sK1
    | r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k1_relat_1(sK1))
    | ~ spl5_40 ),
    inference(equality_resolution,[],[f401])).

fof(f401,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != k1_relat_1(sK1)
        | r2_hidden(sK2(sK0,X1),k1_relat_1(sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k2_funct_1(sK0) = X1
        | r2_hidden(k1_funct_1(sK0,sK3(sK0,X1)),k1_relat_1(sK1)) )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f400])).

fof(f402,plain,
    ( spl5_40
    | ~ spl5_13
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f240,f232,f161,f400])).

% (30955)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f161,plain,
    ( spl5_13
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f232,plain,
    ( spl5_19
  <=> ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | r2_hidden(sK2(sK0,X0),k1_relat_1(sK1))
        | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f240,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(sK0,X1),k1_relat_1(sK1))
        | k1_relat_1(X1) != k1_relat_1(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k2_funct_1(sK0) = X1
        | r2_hidden(k1_funct_1(sK0,sK3(sK0,X1)),k1_relat_1(sK1)) )
    | ~ spl5_13
    | ~ spl5_19 ),
    inference(resolution,[],[f233,f162])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1)) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f233,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | r2_hidden(sK2(sK0,X0),k1_relat_1(sK1))
        | k1_relat_1(X0) != k1_relat_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f232])).

fof(f316,plain,
    ( spl5_29
    | spl5_27
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f293,f286,f100,f90,f85,f300,f313])).

fof(f286,plain,
    ( spl5_26
  <=> ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f293,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f292,f102])).

fof(f292,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | k2_funct_1(sK0) = sK1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f291,f87])).

fof(f291,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK0) = sK1
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f290,f92])).

fof(f290,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK0) = sK1
    | ~ spl5_26 ),
    inference(equality_resolution,[],[f287])).

fof(f287,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f286])).

fof(f307,plain,
    ( spl5_27
    | spl5_28
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f278,f263,f100,f90,f85,f304,f300])).

fof(f263,plain,
    ( spl5_25
  <=> ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | r2_hidden(sK2(sK0,X0),k1_relat_1(sK1))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f278,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f277,f102])).

fof(f277,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | k2_funct_1(sK0) = sK1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f276,f87])).

fof(f276,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK0) = sK1
    | ~ spl5_4
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f275,f92])).

fof(f275,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK0) = sK1
    | ~ spl5_25 ),
    inference(equality_resolution,[],[f264])).

fof(f264,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | r2_hidden(sK2(sK0,X0),k1_relat_1(sK1))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f263])).

fof(f288,plain,
    ( spl5_26
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f224,f110,f95,f80,f75,f286])).

fof(f224,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f223,f112])).

fof(f223,plain,
    ( ! [X0] :
        ( sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f222,f77])).

fof(f222,plain,
    ( ! [X0] :
        ( sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f221,f82])).

fof(f221,plain,
    ( ! [X0] :
        ( sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f54,f97])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
      | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f265,plain,
    ( spl5_25
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f217,f110,f95,f80,f75,f263])).

fof(f217,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | r2_hidden(sK2(sK0,X0),k1_relat_1(sK1))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f216,f112])).

fof(f216,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0,X0),k1_relat_1(sK1))
        | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f215,f112])).

fof(f215,plain,
    ( ! [X0] :
        ( sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f214,f77])).

fof(f214,plain,
    ( ! [X0] :
        ( sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f213,f82])).

fof(f213,plain,
    ( ! [X0] :
        ( sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0))
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f53,f97])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
      | r2_hidden(sK2(X0,X1),k2_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f248,plain,
    ( spl5_21
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f208,f110,f95,f80,f75,f246])).

fof(f208,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f207,f112])).

fof(f207,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f206,f77])).

fof(f206,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f205,f82])).

fof(f205,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f51,f97])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f234,plain,
    ( spl5_19
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f201,f110,f95,f80,f75,f232])).

fof(f201,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK1)
        | r2_hidden(sK2(sK0,X0),k1_relat_1(sK1))
        | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f200,f112])).

fof(f200,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0,X0),k1_relat_1(sK1))
        | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f199,f112])).

fof(f199,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f198,f77])).

fof(f198,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f197,f82])).

fof(f197,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0),k1_relat_1(sK0))
        | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0))
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(sK0) = X0
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f50,f97])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),k2_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f186,plain,
    ( spl5_15
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f182,f95,f80,f75,f184])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f181,f77])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f180,f82])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f178,f97])).

fof(f178,plain,(
    ! [X0,X5] :
      ( ~ v2_funct_1(X0)
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f177,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f177,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f66,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X1,X4) = X5
      | k1_funct_1(X0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f176,plain,
    ( spl5_14
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f172,f110,f95,f80,f75,f174])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(k2_funct_1(sK0),X0),k1_relat_1(sK0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f171,f112])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | r2_hidden(k1_funct_1(k2_funct_1(sK0),X0),k1_relat_1(sK0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f170,f77])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | r2_hidden(k1_funct_1(k2_funct_1(sK0),X0),k1_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f169,f82])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | r2_hidden(k1_funct_1(k2_funct_1(sK0),X0),k1_relat_1(sK0))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f165,f97])).

fof(f165,plain,(
    ! [X4,X0] :
      ( ~ v2_funct_1(X0)
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | r2_hidden(k1_funct_1(k2_funct_1(X0),X4),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f164,f41])).

fof(f164,plain,(
    ! [X4,X0] :
      ( r2_hidden(k1_funct_1(k2_funct_1(X0),X4),k1_relat_1(X0))
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f72,f42])).

fof(f72,plain,(
    ! [X4,X0] :
      ( r2_hidden(k1_funct_1(k2_funct_1(X0),X4),k1_relat_1(X0))
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X4),k1_relat_1(X0))
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | k1_funct_1(X1,X4) != X5
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f163,plain,
    ( spl5_13
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f159,f110,f95,f80,f75,f161])).

fof(f159,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f158,f112])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k1_funct_1(sK0,X0),k2_relat_1(sK0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f157,f77])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k1_funct_1(sK0,X0),k2_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f156,f82])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k1_funct_1(sK0,X0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f152,f97])).

fof(f152,plain,(
    ! [X0,X5] :
      ( ~ v2_funct_1(X0)
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f151,f41])).

fof(f151,plain,(
    ! [X0,X5] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f68,f42])).

fof(f68,plain,(
    ! [X0,X5] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,k2_relat_1(X0))
      | k1_funct_1(X0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f142,plain,
    ( spl5_11
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f134,f110,f95,f80,f75,f140])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f133,f112])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f132,f77])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),X0)) = X0
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f131,f82])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),X0)) = X0
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f61,f97])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(f113,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f37,f110])).

fof(f37,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f40,f100])).

fof(f40,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f35,f95])).

fof(f35,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f93,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f34,f90])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f33,f85])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f32,f80])).

fof(f32,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:17:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.50  % (30941)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.51  % (30933)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.51  % (30936)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.52  % (30932)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.52  % (30943)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.52  % (30951)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.53  % (30940)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.53  % (30945)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.30/0.53  % (30954)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.30/0.53  % (30942)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.30/0.53  % (30956)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.30/0.53  % (30937)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.30/0.53  % (30935)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.30/0.53  % (30946)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.30/0.54  % (30944)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.30/0.54  % (30933)Refutation found. Thanks to Tanya!
% 1.30/0.54  % SZS status Theorem for theBenchmark
% 1.30/0.54  % SZS output start Proof for theBenchmark
% 1.30/0.54  fof(f588,plain,(
% 1.30/0.54    $false),
% 1.30/0.54    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f113,f142,f163,f176,f186,f234,f248,f265,f288,f307,f316,f402,f421,f452,f456,f503,f521,f564,f569,f579,f586,f587])).
% 1.30/0.54  fof(f587,plain,(
% 1.30/0.54    sK3(sK0,sK1) != k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)) | sK2(sK0,sK1) != k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1))) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))),
% 1.30/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.30/0.54  fof(f586,plain,(
% 1.30/0.54    ~spl5_27 | ~spl5_28 | spl5_29 | ~spl5_50),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f585])).
% 1.30/0.54  fof(f585,plain,(
% 1.30/0.54    $false | (~spl5_27 | ~spl5_28 | spl5_29 | ~spl5_50)),
% 1.30/0.54    inference(subsumption_resolution,[],[f584,f519])).
% 1.30/0.54  fof(f519,plain,(
% 1.30/0.54    r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | ~spl5_50),
% 1.30/0.54    inference(avatar_component_clause,[],[f518])).
% 1.30/0.54  fof(f518,plain,(
% 1.30/0.54    spl5_50 <=> r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 1.30/0.54  fof(f584,plain,(
% 1.30/0.54    ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | (~spl5_27 | ~spl5_28 | spl5_29)),
% 1.30/0.54    inference(subsumption_resolution,[],[f571,f314])).
% 1.30/0.54  fof(f314,plain,(
% 1.30/0.54    sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | spl5_29),
% 1.30/0.54    inference(avatar_component_clause,[],[f313])).
% 1.30/0.54  fof(f313,plain,(
% 1.30/0.54    spl5_29 <=> sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.30/0.54  fof(f571,plain,(
% 1.30/0.54    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | (~spl5_27 | ~spl5_28)),
% 1.30/0.54    inference(subsumption_resolution,[],[f317,f306])).
% 1.30/0.54  fof(f306,plain,(
% 1.30/0.54    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | ~spl5_28),
% 1.30/0.54    inference(avatar_component_clause,[],[f304])).
% 1.30/0.54  fof(f304,plain,(
% 1.30/0.54    spl5_28 <=> r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.30/0.54  fof(f317,plain,(
% 1.30/0.54    ~r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | ~spl5_27),
% 1.30/0.54    inference(superposition,[],[f64,f302])).
% 1.30/0.54  fof(f302,plain,(
% 1.30/0.54    sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | ~spl5_27),
% 1.30/0.54    inference(avatar_component_clause,[],[f300])).
% 1.30/0.54  fof(f300,plain,(
% 1.30/0.54    spl5_27 <=> sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.30/0.54  fof(f64,plain,(
% 1.30/0.54    ( ! [X2] : (~r2_hidden(k1_funct_1(sK0,X2),k1_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2 | ~r2_hidden(X2,k1_relat_1(sK0))) )),
% 1.30/0.54    inference(equality_resolution,[],[f38])).
% 1.30/0.54  fof(f38,plain,(
% 1.30/0.54    ( ! [X2,X3] : (k1_funct_1(sK1,X3) = X2 | k1_funct_1(sK0,X2) != X3 | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK0))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  fof(f23,plain,(
% 1.30/0.54    (k2_funct_1(sK0) != sK1 & ! [X2,X3] : (((k1_funct_1(sK0,X2) = X3 | k1_funct_1(sK1,X3) != X2) & (k1_funct_1(sK1,X3) = X2 | k1_funct_1(sK0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK0))) & k2_relat_1(sK0) = k1_relat_1(sK1) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 1.30/0.54  fof(f21,plain,(
% 1.30/0.54    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & ! [X3,X2] : (((k1_funct_1(sK0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(sK0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(X1) = k2_relat_1(sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f22,plain,(
% 1.30/0.54    ? [X1] : (k2_funct_1(sK0) != X1 & ! [X3,X2] : (((k1_funct_1(sK0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(sK0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(X1) = k2_relat_1(sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & ! [X3,X2] : (((k1_funct_1(sK0,X2) = X3 | k1_funct_1(sK1,X3) != X2) & (k1_funct_1(sK1,X3) = X2 | k1_funct_1(sK0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK0))) & k2_relat_1(sK0) = k1_relat_1(sK1) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f20,plain,(
% 1.30/0.54    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.30/0.54    inference(nnf_transformation,[],[f9])).
% 1.30/0.54  fof(f9,plain,(
% 1.30/0.54    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.30/0.54    inference(flattening,[],[f8])).
% 1.30/0.54  fof(f8,plain,(
% 1.30/0.54    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | (~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f7])).
% 1.30/0.54  fof(f7,negated_conjecture,(
% 1.30/0.54    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.30/0.54    inference(negated_conjecture,[],[f6])).
% 1.30/0.54  fof(f6,conjecture,(
% 1.30/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).
% 1.30/0.54  fof(f579,plain,(
% 1.30/0.54    spl5_50 | ~spl5_49 | ~spl5_55),
% 1.30/0.54    inference(avatar_split_clause,[],[f575,f561,f500,f518])).
% 1.30/0.54  fof(f500,plain,(
% 1.30/0.54    spl5_49 <=> sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 1.30/0.54  fof(f561,plain,(
% 1.30/0.54    spl5_55 <=> r2_hidden(k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)),k1_relat_1(sK0))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 1.30/0.54  fof(f575,plain,(
% 1.30/0.54    r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | (~spl5_49 | ~spl5_55)),
% 1.30/0.54    inference(backward_demodulation,[],[f562,f502])).
% 1.30/0.54  fof(f502,plain,(
% 1.30/0.54    sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)) | ~spl5_49),
% 1.30/0.54    inference(avatar_component_clause,[],[f500])).
% 1.30/0.54  fof(f562,plain,(
% 1.30/0.54    r2_hidden(k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)),k1_relat_1(sK0)) | ~spl5_55),
% 1.30/0.54    inference(avatar_component_clause,[],[f561])).
% 1.30/0.54  fof(f569,plain,(
% 1.30/0.54    ~spl5_14 | ~spl5_28 | spl5_55),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f568])).
% 1.30/0.54  fof(f568,plain,(
% 1.30/0.54    $false | (~spl5_14 | ~spl5_28 | spl5_55)),
% 1.30/0.54    inference(subsumption_resolution,[],[f566,f306])).
% 1.30/0.54  fof(f566,plain,(
% 1.30/0.54    ~r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | (~spl5_14 | spl5_55)),
% 1.30/0.54    inference(resolution,[],[f563,f175])).
% 1.30/0.54  fof(f175,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(k2_funct_1(sK0),X0),k1_relat_1(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl5_14),
% 1.30/0.54    inference(avatar_component_clause,[],[f174])).
% 1.30/0.54  fof(f174,plain,(
% 1.30/0.54    spl5_14 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(k2_funct_1(sK0),X0),k1_relat_1(sK0)))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.30/0.54  fof(f563,plain,(
% 1.30/0.54    ~r2_hidden(k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)),k1_relat_1(sK0)) | spl5_55),
% 1.30/0.54    inference(avatar_component_clause,[],[f561])).
% 1.30/0.54  fof(f564,plain,(
% 1.30/0.54    ~spl5_55 | spl5_49 | ~spl5_28 | ~spl5_29 | ~spl5_43),
% 1.30/0.54    inference(avatar_split_clause,[],[f557,f449,f313,f304,f500,f561])).
% 1.30/0.54  fof(f449,plain,(
% 1.30/0.54    spl5_43 <=> sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 1.30/0.54  fof(f557,plain,(
% 1.30/0.54    sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)) | ~r2_hidden(k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)),k1_relat_1(sK0)) | (~spl5_28 | ~spl5_29 | ~spl5_43)),
% 1.30/0.54    inference(forward_demodulation,[],[f458,f315])).
% 1.30/0.54  fof(f315,plain,(
% 1.30/0.54    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~spl5_29),
% 1.30/0.54    inference(avatar_component_clause,[],[f313])).
% 1.30/0.54  fof(f458,plain,(
% 1.30/0.54    k1_funct_1(sK1,sK2(sK0,sK1)) = k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)) | ~r2_hidden(k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)),k1_relat_1(sK0)) | (~spl5_28 | ~spl5_43)),
% 1.30/0.54    inference(subsumption_resolution,[],[f457,f306])).
% 1.30/0.54  fof(f457,plain,(
% 1.30/0.54    ~r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | k1_funct_1(sK1,sK2(sK0,sK1)) = k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)) | ~r2_hidden(k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)),k1_relat_1(sK0)) | ~spl5_43),
% 1.30/0.54    inference(superposition,[],[f64,f451])).
% 1.30/0.54  fof(f451,plain,(
% 1.30/0.54    sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1))) | ~spl5_43),
% 1.30/0.54    inference(avatar_component_clause,[],[f449])).
% 1.30/0.54  fof(f521,plain,(
% 1.30/0.54    ~spl5_50 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8 | ~spl5_27 | ~spl5_28 | ~spl5_29),
% 1.30/0.54    inference(avatar_split_clause,[],[f516,f313,f304,f300,f110,f100,f95,f90,f85,f80,f75,f518])).
% 1.30/0.54  fof(f75,plain,(
% 1.30/0.54    spl5_1 <=> v1_relat_1(sK0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.30/0.54  fof(f80,plain,(
% 1.30/0.54    spl5_2 <=> v1_funct_1(sK0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.30/0.54  fof(f85,plain,(
% 1.30/0.54    spl5_3 <=> v1_relat_1(sK1)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.30/0.54  fof(f90,plain,(
% 1.30/0.54    spl5_4 <=> v1_funct_1(sK1)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.30/0.54  fof(f95,plain,(
% 1.30/0.54    spl5_5 <=> v2_funct_1(sK0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.30/0.54  fof(f100,plain,(
% 1.30/0.54    spl5_6 <=> k2_funct_1(sK0) = sK1),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.30/0.54  fof(f110,plain,(
% 1.30/0.54    spl5_8 <=> k2_relat_1(sK0) = k1_relat_1(sK1)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.30/0.54  fof(f516,plain,(
% 1.30/0.54    ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8 | ~spl5_27 | ~spl5_28 | ~spl5_29)),
% 1.30/0.54    inference(subsumption_resolution,[],[f515,f306])).
% 1.30/0.54  fof(f515,plain,(
% 1.30/0.54    ~r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8 | ~spl5_27 | ~spl5_29)),
% 1.30/0.54    inference(forward_demodulation,[],[f514,f112])).
% 1.30/0.54  fof(f112,plain,(
% 1.30/0.54    k2_relat_1(sK0) = k1_relat_1(sK1) | ~spl5_8),
% 1.30/0.54    inference(avatar_component_clause,[],[f110])).
% 1.30/0.54  fof(f514,plain,(
% 1.30/0.54    ~r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8 | ~spl5_27 | ~spl5_29)),
% 1.30/0.54    inference(subsumption_resolution,[],[f513,f77])).
% 1.30/0.54  fof(f77,plain,(
% 1.30/0.54    v1_relat_1(sK0) | ~spl5_1),
% 1.30/0.54    inference(avatar_component_clause,[],[f75])).
% 1.30/0.54  fof(f513,plain,(
% 1.30/0.54    ~r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8 | ~spl5_27 | ~spl5_29)),
% 1.30/0.54    inference(subsumption_resolution,[],[f512,f82])).
% 1.30/0.54  fof(f82,plain,(
% 1.30/0.54    v1_funct_1(sK0) | ~spl5_2),
% 1.30/0.54    inference(avatar_component_clause,[],[f80])).
% 1.30/0.54  fof(f512,plain,(
% 1.30/0.54    ~r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8 | ~spl5_27 | ~spl5_29)),
% 1.30/0.54    inference(subsumption_resolution,[],[f511,f97])).
% 1.30/0.54  fof(f97,plain,(
% 1.30/0.54    v2_funct_1(sK0) | ~spl5_5),
% 1.30/0.54    inference(avatar_component_clause,[],[f95])).
% 1.30/0.54  fof(f511,plain,(
% 1.30/0.54    ~r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_8 | ~spl5_27 | ~spl5_29)),
% 1.30/0.54    inference(subsumption_resolution,[],[f510,f87])).
% 1.30/0.54  fof(f87,plain,(
% 1.30/0.54    v1_relat_1(sK1) | ~spl5_3),
% 1.30/0.54    inference(avatar_component_clause,[],[f85])).
% 1.30/0.54  fof(f510,plain,(
% 1.30/0.54    ~r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | ~v1_relat_1(sK1) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl5_4 | spl5_6 | ~spl5_8 | ~spl5_27 | ~spl5_29)),
% 1.30/0.54    inference(subsumption_resolution,[],[f509,f92])).
% 1.30/0.54  fof(f92,plain,(
% 1.30/0.54    v1_funct_1(sK1) | ~spl5_4),
% 1.30/0.54    inference(avatar_component_clause,[],[f90])).
% 1.30/0.54  fof(f509,plain,(
% 1.30/0.54    ~r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl5_6 | ~spl5_8 | ~spl5_27 | ~spl5_29)),
% 1.30/0.54    inference(subsumption_resolution,[],[f508,f112])).
% 1.30/0.54  fof(f508,plain,(
% 1.30/0.54    ~r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl5_6 | ~spl5_27 | ~spl5_29)),
% 1.30/0.54    inference(subsumption_resolution,[],[f507,f302])).
% 1.30/0.54  fof(f507,plain,(
% 1.30/0.54    ~r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl5_6 | ~spl5_29)),
% 1.30/0.54    inference(subsumption_resolution,[],[f506,f102])).
% 1.30/0.54  fof(f102,plain,(
% 1.30/0.54    k2_funct_1(sK0) != sK1 | spl5_6),
% 1.30/0.54    inference(avatar_component_clause,[],[f100])).
% 1.30/0.54  fof(f506,plain,(
% 1.30/0.54    k2_funct_1(sK0) = sK1 | ~r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl5_29),
% 1.30/0.54    inference(trivial_inequality_removal,[],[f504])).
% 1.30/0.54  fof(f504,plain,(
% 1.30/0.54    sK3(sK0,sK1) != sK3(sK0,sK1) | k2_funct_1(sK0) = sK1 | ~r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl5_29),
% 1.30/0.54    inference(superposition,[],[f58,f315])).
% 1.30/0.54  fof(f58,plain,(
% 1.30/0.54    ( ! [X0,X1] : (sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k2_funct_1(X0) = X1 | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f28])).
% 1.30/0.54  fof(f28,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0))) & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | ((sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0))) & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & ((k1_funct_1(X0,X5) = X4 & r2_hidden(X5,k1_relat_1(X0))) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f27])).
% 1.30/0.54  fof(f27,plain,(
% 1.30/0.54    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) => (((sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0))) & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | ((sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0))) & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k2_relat_1(X0)))))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f26,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & ((k1_funct_1(X0,X5) = X4 & r2_hidden(X5,k1_relat_1(X0))) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(rectify,[],[f25])).
% 1.30/0.54  fof(f25,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(flattening,[],[f24])).
% 1.30/0.54  fof(f24,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(nnf_transformation,[],[f15])).
% 1.30/0.54  fof(f15,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(flattening,[],[f14])).
% 1.30/0.54  fof(f14,plain,(
% 1.30/0.54    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f2])).
% 1.30/0.54  fof(f2,axiom,(
% 1.30/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).
% 1.30/0.54  fof(f503,plain,(
% 1.30/0.54    spl5_29 | spl5_49 | ~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_27 | ~spl5_44),
% 1.30/0.54    inference(avatar_split_clause,[],[f464,f454,f300,f100,f90,f85,f500,f313])).
% 1.30/0.54  fof(f454,plain,(
% 1.30/0.54    spl5_44 <=> ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | sK3(sK0,X0) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,X0))))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 1.30/0.54  fof(f464,plain,(
% 1.30/0.54    sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1)) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | (~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_27 | ~spl5_44)),
% 1.30/0.54    inference(forward_demodulation,[],[f463,f302])).
% 1.30/0.54  fof(f463,plain,(
% 1.30/0.54    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,sK1))) | (~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_44)),
% 1.30/0.54    inference(subsumption_resolution,[],[f462,f102])).
% 1.30/0.54  fof(f462,plain,(
% 1.30/0.54    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | k2_funct_1(sK0) = sK1 | sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,sK1))) | (~spl5_3 | ~spl5_4 | ~spl5_44)),
% 1.30/0.54    inference(subsumption_resolution,[],[f461,f87])).
% 1.30/0.54  fof(f461,plain,(
% 1.30/0.54    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~v1_relat_1(sK1) | k2_funct_1(sK0) = sK1 | sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,sK1))) | (~spl5_4 | ~spl5_44)),
% 1.30/0.54    inference(subsumption_resolution,[],[f460,f92])).
% 1.30/0.54  fof(f460,plain,(
% 1.30/0.54    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK0) = sK1 | sK3(sK0,sK1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,sK1))) | ~spl5_44),
% 1.30/0.54    inference(equality_resolution,[],[f455])).
% 1.30/0.54  fof(f455,plain,(
% 1.30/0.54    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | sK3(sK0,X0) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,X0)))) ) | ~spl5_44),
% 1.30/0.54    inference(avatar_component_clause,[],[f454])).
% 1.30/0.54  fof(f456,plain,(
% 1.30/0.54    spl5_44 | ~spl5_15 | ~spl5_21),
% 1.30/0.54    inference(avatar_split_clause,[],[f272,f246,f184,f454])).
% 1.30/0.54  fof(f184,plain,(
% 1.30/0.54    spl5_15 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.30/0.54  fof(f246,plain,(
% 1.30/0.54    spl5_21 <=> ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.30/0.54  fof(f272,plain,(
% 1.30/0.54    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | sK3(sK0,X0) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK3(sK0,X0)))) ) | (~spl5_15 | ~spl5_21)),
% 1.30/0.54    inference(resolution,[],[f247,f185])).
% 1.30/0.54  fof(f185,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0) ) | ~spl5_15),
% 1.30/0.54    inference(avatar_component_clause,[],[f184])).
% 1.30/0.54  fof(f247,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | k1_relat_1(X0) != k1_relat_1(sK1) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | ~spl5_21),
% 1.30/0.54    inference(avatar_component_clause,[],[f246])).
% 1.30/0.54  fof(f452,plain,(
% 1.30/0.54    spl5_43 | ~spl5_11 | ~spl5_28),
% 1.30/0.54    inference(avatar_split_clause,[],[f425,f304,f140,f449])).
% 1.30/0.54  fof(f140,plain,(
% 1.30/0.54    spl5_11 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),X0)) = X0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.30/0.54  fof(f425,plain,(
% 1.30/0.54    sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK2(sK0,sK1))) | (~spl5_11 | ~spl5_28)),
% 1.30/0.54    inference(resolution,[],[f306,f141])).
% 1.30/0.54  fof(f141,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),X0)) = X0) ) | ~spl5_11),
% 1.30/0.54    inference(avatar_component_clause,[],[f140])).
% 1.30/0.54  fof(f421,plain,(
% 1.30/0.54    spl5_28 | ~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_27 | ~spl5_40),
% 1.30/0.54    inference(avatar_split_clause,[],[f420,f400,f300,f100,f90,f85,f304])).
% 1.30/0.54  fof(f400,plain,(
% 1.30/0.54    spl5_40 <=> ! [X1] : (r2_hidden(sK2(sK0,X1),k1_relat_1(sK1)) | k1_relat_1(X1) != k1_relat_1(sK1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_funct_1(sK0) = X1 | r2_hidden(k1_funct_1(sK0,sK3(sK0,X1)),k1_relat_1(sK1)))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 1.30/0.54  fof(f420,plain,(
% 1.30/0.54    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | (~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_27 | ~spl5_40)),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f419])).
% 1.30/0.54  fof(f419,plain,(
% 1.30/0.54    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | (~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_27 | ~spl5_40)),
% 1.30/0.54    inference(forward_demodulation,[],[f418,f302])).
% 1.30/0.54  fof(f418,plain,(
% 1.30/0.54    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k1_relat_1(sK1)) | (~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_40)),
% 1.30/0.54    inference(subsumption_resolution,[],[f417,f102])).
% 1.30/0.54  fof(f417,plain,(
% 1.30/0.54    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | k2_funct_1(sK0) = sK1 | r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k1_relat_1(sK1)) | (~spl5_3 | ~spl5_4 | ~spl5_40)),
% 1.30/0.54    inference(subsumption_resolution,[],[f416,f87])).
% 1.30/0.54  fof(f416,plain,(
% 1.30/0.54    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | k2_funct_1(sK0) = sK1 | r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k1_relat_1(sK1)) | (~spl5_4 | ~spl5_40)),
% 1.30/0.54    inference(subsumption_resolution,[],[f408,f92])).
% 1.30/0.54  fof(f408,plain,(
% 1.30/0.54    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK0) = sK1 | r2_hidden(k1_funct_1(sK0,sK3(sK0,sK1)),k1_relat_1(sK1)) | ~spl5_40),
% 1.30/0.54    inference(equality_resolution,[],[f401])).
% 1.30/0.54  fof(f401,plain,(
% 1.30/0.54    ( ! [X1] : (k1_relat_1(X1) != k1_relat_1(sK1) | r2_hidden(sK2(sK0,X1),k1_relat_1(sK1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_funct_1(sK0) = X1 | r2_hidden(k1_funct_1(sK0,sK3(sK0,X1)),k1_relat_1(sK1))) ) | ~spl5_40),
% 1.30/0.54    inference(avatar_component_clause,[],[f400])).
% 1.30/0.54  fof(f402,plain,(
% 1.30/0.54    spl5_40 | ~spl5_13 | ~spl5_19),
% 1.30/0.54    inference(avatar_split_clause,[],[f240,f232,f161,f400])).
% 1.30/0.54  % (30955)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.30/0.54  fof(f161,plain,(
% 1.30/0.54    spl5_13 <=> ! [X0] : (r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK0)))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.30/0.54  fof(f232,plain,(
% 1.30/0.54    spl5_19 <=> ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | r2_hidden(sK2(sK0,X0),k1_relat_1(sK1)) | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.30/0.54  fof(f240,plain,(
% 1.30/0.54    ( ! [X1] : (r2_hidden(sK2(sK0,X1),k1_relat_1(sK1)) | k1_relat_1(X1) != k1_relat_1(sK1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_funct_1(sK0) = X1 | r2_hidden(k1_funct_1(sK0,sK3(sK0,X1)),k1_relat_1(sK1))) ) | (~spl5_13 | ~spl5_19)),
% 1.30/0.54    inference(resolution,[],[f233,f162])).
% 1.30/0.54  fof(f162,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1))) ) | ~spl5_13),
% 1.30/0.54    inference(avatar_component_clause,[],[f161])).
% 1.30/0.54  fof(f233,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | r2_hidden(sK2(sK0,X0),k1_relat_1(sK1)) | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | ~spl5_19),
% 1.30/0.54    inference(avatar_component_clause,[],[f232])).
% 1.30/0.54  fof(f316,plain,(
% 1.30/0.54    spl5_29 | spl5_27 | ~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_26),
% 1.30/0.54    inference(avatar_split_clause,[],[f293,f286,f100,f90,f85,f300,f313])).
% 1.30/0.54  fof(f286,plain,(
% 1.30/0.54    spl5_26 <=> ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.30/0.54  fof(f293,plain,(
% 1.30/0.54    sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | (~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_26)),
% 1.30/0.54    inference(subsumption_resolution,[],[f292,f102])).
% 1.30/0.54  fof(f292,plain,(
% 1.30/0.54    sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | k2_funct_1(sK0) = sK1 | (~spl5_3 | ~spl5_4 | ~spl5_26)),
% 1.30/0.54    inference(subsumption_resolution,[],[f291,f87])).
% 1.30/0.54  fof(f291,plain,(
% 1.30/0.54    sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~v1_relat_1(sK1) | k2_funct_1(sK0) = sK1 | (~spl5_4 | ~spl5_26)),
% 1.30/0.54    inference(subsumption_resolution,[],[f290,f92])).
% 1.30/0.54  fof(f290,plain,(
% 1.30/0.54    sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK0) = sK1 | ~spl5_26),
% 1.30/0.54    inference(equality_resolution,[],[f287])).
% 1.30/0.54  fof(f287,plain,(
% 1.30/0.54    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | ~spl5_26),
% 1.30/0.54    inference(avatar_component_clause,[],[f286])).
% 1.30/0.54  fof(f307,plain,(
% 1.30/0.54    spl5_27 | spl5_28 | ~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_25),
% 1.30/0.54    inference(avatar_split_clause,[],[f278,f263,f100,f90,f85,f304,f300])).
% 1.30/0.54  fof(f263,plain,(
% 1.30/0.54    spl5_25 <=> ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | r2_hidden(sK2(sK0,X0),k1_relat_1(sK1)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.30/0.54  fof(f278,plain,(
% 1.30/0.54    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | (~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_25)),
% 1.30/0.54    inference(subsumption_resolution,[],[f277,f102])).
% 1.30/0.54  fof(f277,plain,(
% 1.30/0.54    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | k2_funct_1(sK0) = sK1 | (~spl5_3 | ~spl5_4 | ~spl5_25)),
% 1.30/0.54    inference(subsumption_resolution,[],[f276,f87])).
% 1.30/0.54  fof(f276,plain,(
% 1.30/0.54    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | ~v1_relat_1(sK1) | k2_funct_1(sK0) = sK1 | (~spl5_4 | ~spl5_25)),
% 1.30/0.54    inference(subsumption_resolution,[],[f275,f92])).
% 1.30/0.54  fof(f275,plain,(
% 1.30/0.54    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK0) = sK1 | ~spl5_25),
% 1.30/0.54    inference(equality_resolution,[],[f264])).
% 1.30/0.54  fof(f264,plain,(
% 1.30/0.54    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | r2_hidden(sK2(sK0,X0),k1_relat_1(sK1)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | ~spl5_25),
% 1.30/0.54    inference(avatar_component_clause,[],[f263])).
% 1.30/0.54  fof(f288,plain,(
% 1.30/0.54    spl5_26 | ~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8),
% 1.30/0.54    inference(avatar_split_clause,[],[f224,f110,f95,f80,f75,f286])).
% 1.30/0.54  fof(f224,plain,(
% 1.30/0.54    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8)),
% 1.30/0.54    inference(forward_demodulation,[],[f223,f112])).
% 1.30/0.54  fof(f223,plain,(
% 1.30/0.54    ( ! [X0] : (sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f222,f77])).
% 1.30/0.54  fof(f222,plain,(
% 1.30/0.54    ( ! [X0] : (sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f221,f82])).
% 1.30/0.54  fof(f221,plain,(
% 1.30/0.54    ( ! [X0] : (sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | ~spl5_5),
% 1.30/0.54    inference(resolution,[],[f54,f97])).
% 1.30/0.54  fof(f54,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~v2_funct_1(X0) | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_funct_1(X0) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f28])).
% 1.30/0.54  fof(f265,plain,(
% 1.30/0.54    spl5_25 | ~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8),
% 1.30/0.54    inference(avatar_split_clause,[],[f217,f110,f95,f80,f75,f263])).
% 1.30/0.54  fof(f217,plain,(
% 1.30/0.54    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | r2_hidden(sK2(sK0,X0),k1_relat_1(sK1)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8)),
% 1.30/0.54    inference(forward_demodulation,[],[f216,f112])).
% 1.30/0.54  fof(f216,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK2(sK0,X0),k1_relat_1(sK1)) | sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8)),
% 1.30/0.54    inference(forward_demodulation,[],[f215,f112])).
% 1.30/0.54  fof(f215,plain,(
% 1.30/0.54    ( ! [X0] : (sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f214,f77])).
% 1.30/0.54  fof(f214,plain,(
% 1.30/0.54    ( ! [X0] : (sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f213,f82])).
% 1.30/0.54  fof(f213,plain,(
% 1.30/0.54    ( ! [X0] : (sK2(sK0,X0) = k1_funct_1(sK0,sK3(sK0,X0)) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | ~spl5_5),
% 1.30/0.54    inference(resolution,[],[f53,f97])).
% 1.30/0.54  fof(f53,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~v2_funct_1(X0) | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_funct_1(X0) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f28])).
% 1.30/0.54  fof(f248,plain,(
% 1.30/0.54    spl5_21 | ~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8),
% 1.30/0.54    inference(avatar_split_clause,[],[f208,f110,f95,f80,f75,f246])).
% 1.30/0.54  fof(f208,plain,(
% 1.30/0.54    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8)),
% 1.30/0.54    inference(forward_demodulation,[],[f207,f112])).
% 1.30/0.54  fof(f207,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f206,f77])).
% 1.30/0.54  fof(f206,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f205,f82])).
% 1.30/0.54  fof(f205,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | sK3(sK0,X0) = k1_funct_1(X0,sK2(sK0,X0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | ~spl5_5),
% 1.30/0.54    inference(resolution,[],[f51,f97])).
% 1.30/0.54  fof(f51,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~v2_funct_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_funct_1(X0) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f28])).
% 1.30/0.54  fof(f234,plain,(
% 1.30/0.54    spl5_19 | ~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8),
% 1.30/0.54    inference(avatar_split_clause,[],[f201,f110,f95,f80,f75,f232])).
% 1.30/0.54  fof(f201,plain,(
% 1.30/0.54    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK1) | r2_hidden(sK2(sK0,X0),k1_relat_1(sK1)) | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8)),
% 1.30/0.54    inference(forward_demodulation,[],[f200,f112])).
% 1.30/0.54  fof(f200,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK2(sK0,X0),k1_relat_1(sK1)) | r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8)),
% 1.30/0.54    inference(forward_demodulation,[],[f199,f112])).
% 1.30/0.54  fof(f199,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f198,f77])).
% 1.30/0.54  fof(f198,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f197,f82])).
% 1.30/0.54  fof(f197,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK3(sK0,X0),k1_relat_1(sK0)) | r2_hidden(sK2(sK0,X0),k2_relat_1(sK0)) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK0) = X0 | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | ~spl5_5),
% 1.30/0.54    inference(resolution,[],[f50,f97])).
% 1.30/0.54  fof(f50,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~v2_funct_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_funct_1(X0) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f28])).
% 1.30/0.54  fof(f186,plain,(
% 1.30/0.54    spl5_15 | ~spl5_1 | ~spl5_2 | ~spl5_5),
% 1.30/0.54    inference(avatar_split_clause,[],[f182,f95,f80,f75,f184])).
% 1.30/0.54  fof(f182,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f181,f77])).
% 1.30/0.54  fof(f181,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0 | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f180,f82])).
% 1.30/0.54  fof(f180,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0 | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | ~spl5_5),
% 1.30/0.54    inference(resolution,[],[f178,f97])).
% 1.30/0.54  fof(f178,plain,(
% 1.30/0.54    ( ! [X0,X5] : (~v2_funct_1(X0) | ~r2_hidden(X5,k1_relat_1(X0)) | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f177,f41])).
% 1.30/0.54  fof(f41,plain,(
% 1.30/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f11])).
% 1.30/0.54  fof(f11,plain,(
% 1.30/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(flattening,[],[f10])).
% 1.30/0.54  fof(f10,plain,(
% 1.30/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f1])).
% 1.30/0.54  fof(f1,axiom,(
% 1.30/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.30/0.54  fof(f177,plain,(
% 1.30/0.54    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f66,f42])).
% 1.30/0.54  fof(f42,plain,(
% 1.30/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f11])).
% 1.30/0.54  fof(f66,plain,(
% 1.30/0.54    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(equality_resolution,[],[f65])).
% 1.30/0.54  fof(f65,plain,(
% 1.30/0.54    ( ! [X0,X5,X1] : (k1_funct_1(X1,k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(equality_resolution,[],[f49])).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    ( ! [X4,X0,X5,X1] : (k1_funct_1(X1,X4) = X5 | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f28])).
% 1.30/0.54  fof(f176,plain,(
% 1.30/0.54    spl5_14 | ~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8),
% 1.30/0.54    inference(avatar_split_clause,[],[f172,f110,f95,f80,f75,f174])).
% 1.30/0.54  fof(f172,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(k2_funct_1(sK0),X0),k1_relat_1(sK0))) ) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8)),
% 1.30/0.54    inference(forward_demodulation,[],[f171,f112])).
% 1.30/0.54  fof(f171,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | r2_hidden(k1_funct_1(k2_funct_1(sK0),X0),k1_relat_1(sK0))) ) | (~spl5_1 | ~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f170,f77])).
% 1.30/0.54  fof(f170,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | r2_hidden(k1_funct_1(k2_funct_1(sK0),X0),k1_relat_1(sK0)) | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f169,f82])).
% 1.30/0.54  fof(f169,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | r2_hidden(k1_funct_1(k2_funct_1(sK0),X0),k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | ~spl5_5),
% 1.30/0.54    inference(resolution,[],[f165,f97])).
% 1.30/0.54  fof(f165,plain,(
% 1.30/0.54    ( ! [X4,X0] : (~v2_funct_1(X0) | ~r2_hidden(X4,k2_relat_1(X0)) | r2_hidden(k1_funct_1(k2_funct_1(X0),X4),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f164,f41])).
% 1.30/0.54  fof(f164,plain,(
% 1.30/0.54    ( ! [X4,X0] : (r2_hidden(k1_funct_1(k2_funct_1(X0),X4),k1_relat_1(X0)) | ~r2_hidden(X4,k2_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f72,f42])).
% 1.30/0.54  fof(f72,plain,(
% 1.30/0.54    ( ! [X4,X0] : (r2_hidden(k1_funct_1(k2_funct_1(X0),X4),k1_relat_1(X0)) | ~r2_hidden(X4,k2_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(equality_resolution,[],[f71])).
% 1.30/0.54  fof(f71,plain,(
% 1.30/0.54    ( ! [X4,X0,X1] : (r2_hidden(k1_funct_1(X1,X4),k1_relat_1(X0)) | ~r2_hidden(X4,k2_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(equality_resolution,[],[f46])).
% 1.30/0.54  fof(f46,plain,(
% 1.30/0.54    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,k1_relat_1(X0)) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f28])).
% 1.30/0.54  fof(f163,plain,(
% 1.30/0.54    spl5_13 | ~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8),
% 1.30/0.54    inference(avatar_split_clause,[],[f159,f110,f95,f80,f75,f161])).
% 1.30/0.54  fof(f159,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK0))) ) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8)),
% 1.30/0.54    inference(forward_demodulation,[],[f158,f112])).
% 1.30/0.54  fof(f158,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k1_funct_1(sK0,X0),k2_relat_1(sK0))) ) | (~spl5_1 | ~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f157,f77])).
% 1.30/0.54  fof(f157,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k1_funct_1(sK0,X0),k2_relat_1(sK0)) | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f156,f82])).
% 1.30/0.54  fof(f156,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k1_funct_1(sK0,X0),k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | ~spl5_5),
% 1.30/0.54    inference(resolution,[],[f152,f97])).
% 1.30/0.54  fof(f152,plain,(
% 1.30/0.54    ( ! [X0,X5] : (~v2_funct_1(X0) | ~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f151,f41])).
% 1.30/0.54  fof(f151,plain,(
% 1.30/0.54    ( ! [X0,X5] : (r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0)) | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f68,f42])).
% 1.30/0.54  fof(f68,plain,(
% 1.30/0.54    ( ! [X0,X5] : (r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0)) | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(equality_resolution,[],[f67])).
% 1.30/0.54  fof(f67,plain,(
% 1.30/0.54    ( ! [X0,X5,X1] : (r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0)) | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(equality_resolution,[],[f48])).
% 1.30/0.54  fof(f48,plain,(
% 1.30/0.54    ( ! [X4,X0,X5,X1] : (r2_hidden(X4,k2_relat_1(X0)) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f28])).
% 1.30/0.54  fof(f142,plain,(
% 1.30/0.54    spl5_11 | ~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8),
% 1.30/0.54    inference(avatar_split_clause,[],[f134,f110,f95,f80,f75,f140])).
% 1.30/0.54  fof(f134,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),X0)) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_8)),
% 1.30/0.54    inference(forward_demodulation,[],[f133,f112])).
% 1.30/0.54  fof(f133,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),X0)) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f132,f77])).
% 1.30/0.54  fof(f132,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),X0)) = X0 | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f131,f82])).
% 1.30/0.54  fof(f131,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),X0)) = X0 | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | ~spl5_5),
% 1.30/0.54    inference(resolution,[],[f61,f97])).
% 1.30/0.54  fof(f61,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~v2_funct_1(X1) | ~r2_hidden(X0,k2_relat_1(X1)) | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f19])).
% 1.30/0.54  fof(f19,plain,(
% 1.30/0.54    ! [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.30/0.54    inference(flattening,[],[f18])).
% 1.30/0.54  fof(f18,plain,(
% 1.30/0.54    ! [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | (~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.30/0.54    inference(ennf_transformation,[],[f4])).
% 1.30/0.54  fof(f4,axiom,(
% 1.30/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).
% 1.30/0.54  fof(f113,plain,(
% 1.30/0.54    spl5_8),
% 1.30/0.54    inference(avatar_split_clause,[],[f37,f110])).
% 1.30/0.54  fof(f37,plain,(
% 1.30/0.54    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  fof(f103,plain,(
% 1.30/0.54    ~spl5_6),
% 1.30/0.54    inference(avatar_split_clause,[],[f40,f100])).
% 1.30/0.54  fof(f40,plain,(
% 1.30/0.54    k2_funct_1(sK0) != sK1),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  fof(f98,plain,(
% 1.30/0.54    spl5_5),
% 1.30/0.54    inference(avatar_split_clause,[],[f35,f95])).
% 1.30/0.54  fof(f35,plain,(
% 1.30/0.54    v2_funct_1(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  fof(f93,plain,(
% 1.30/0.54    spl5_4),
% 1.30/0.54    inference(avatar_split_clause,[],[f34,f90])).
% 1.30/0.54  fof(f34,plain,(
% 1.30/0.54    v1_funct_1(sK1)),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  fof(f88,plain,(
% 1.30/0.54    spl5_3),
% 1.30/0.54    inference(avatar_split_clause,[],[f33,f85])).
% 1.30/0.54  fof(f33,plain,(
% 1.30/0.54    v1_relat_1(sK1)),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  fof(f83,plain,(
% 1.30/0.54    spl5_2),
% 1.30/0.54    inference(avatar_split_clause,[],[f32,f80])).
% 1.30/0.54  fof(f32,plain,(
% 1.30/0.54    v1_funct_1(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  fof(f78,plain,(
% 1.30/0.54    spl5_1),
% 1.30/0.54    inference(avatar_split_clause,[],[f31,f75])).
% 1.30/0.54  fof(f31,plain,(
% 1.30/0.54    v1_relat_1(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  % SZS output end Proof for theBenchmark
% 1.30/0.54  % (30933)------------------------------
% 1.30/0.54  % (30933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (30933)Termination reason: Refutation
% 1.30/0.54  
% 1.30/0.54  % (30933)Memory used [KB]: 6524
% 1.30/0.54  % (30933)Time elapsed: 0.096 s
% 1.30/0.54  % (30933)------------------------------
% 1.30/0.54  % (30933)------------------------------
% 1.30/0.54  % (30938)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.30/0.54  % (30930)Success in time 0.173 s
%------------------------------------------------------------------------------
