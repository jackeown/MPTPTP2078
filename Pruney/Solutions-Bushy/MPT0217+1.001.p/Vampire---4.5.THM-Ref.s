%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0217+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:33 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 157 expanded)
%              Number of leaves         :   14 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  219 ( 787 expanded)
%              Number of equality atoms :  112 ( 501 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f47,f55,f64,f69,f78,f97,f107,f114])).

fof(f114,plain,
    ( spl5_8
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f110,f77])).

fof(f77,plain,
    ( sK0 != sK1
    | spl5_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_8
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f110,plain,
    ( sK0 = sK1
    | ~ spl5_11 ),
    inference(resolution,[],[f106,f24])).

fof(f24,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f10])).

fof(f10,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK0,sK1))
        | sK1 = X0 )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK0,sK1))
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f107,plain,
    ( spl5_11
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f102,f94,f105])).

fof(f94,plain,
    ( spl5_10
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK0,sK1))
        | sK1 = X0 )
    | ~ spl5_10 ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK0,sK1))
        | sK1 = X0
        | sK1 = X0 )
    | ~ spl5_10 ),
    inference(superposition,[],[f25,f96])).

fof(f96,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f25,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f97,plain,
    ( spl5_10
    | spl5_2
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f87,f66,f52,f32,f94])).

fof(f32,plain,
    ( spl5_2
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f52,plain,
    ( spl5_5
  <=> r2_hidden(sK3,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f66,plain,
    ( spl5_7
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f87,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1)
    | spl5_2
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f68,f85])).

fof(f85,plain,
    ( sK1 = sK3
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f84,f34])).

fof(f34,plain,
    ( sK0 != sK3
    | spl5_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f84,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl5_5 ),
    inference(resolution,[],[f54,f25])).

fof(f54,plain,
    ( r2_hidden(sK3,k2_tarski(sK0,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f68,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK1,sK3)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f78,plain,
    ( ~ spl5_8
    | spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f70,f61,f27,f75])).

fof(f27,plain,
    ( spl5_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f61,plain,
    ( spl5_6
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f70,plain,
    ( sK0 != sK1
    | spl5_1
    | ~ spl5_6 ),
    inference(superposition,[],[f29,f63])).

fof(f63,plain,
    ( sK1 = sK2
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f29,plain,
    ( sK0 != sK2
    | spl5_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f69,plain,
    ( spl5_7
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f59,f44,f37,f27,f66])).

fof(f37,plain,
    ( spl5_3
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f44,plain,
    ( spl5_4
  <=> r2_hidden(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f59,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK1,sK3)
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f39,f57])).

fof(f57,plain,
    ( sK1 = sK2
    | spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f56,f29])).

fof(f56,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl5_4 ),
    inference(resolution,[],[f46,f25])).

fof(f46,plain,
    ( r2_hidden(sK2,k2_tarski(sK0,sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f39,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f64,plain,
    ( spl5_6
    | spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f57,f44,f27,f61])).

fof(f55,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f42,f37,f52])).

fof(f42,plain,
    ( r2_hidden(sK3,k2_tarski(sK0,sK1))
    | ~ spl5_3 ),
    inference(superposition,[],[f22,f39])).

fof(f22,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f41,f37,f44])).

fof(f41,plain,
    ( r2_hidden(sK2,k2_tarski(sK0,sK1))
    | ~ spl5_3 ),
    inference(superposition,[],[f24,f39])).

fof(f40,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f12,f37])).

fof(f12,plain,(
    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) )
   => ( sK0 != sK3
      & sK0 != sK2
      & k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_zfmisc_1)).

fof(f35,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f14,f32])).

fof(f14,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
