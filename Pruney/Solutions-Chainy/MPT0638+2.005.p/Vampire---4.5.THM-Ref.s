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
% DateTime   : Thu Dec  3 12:52:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 165 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  311 ( 647 expanded)
%              Number of equality atoms :   64 ( 177 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f78,f99,f105,f109,f177,f201,f210])).

fof(f210,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | spl6_10
    | ~ spl6_21
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | spl6_10
    | ~ spl6_21
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f208,f104])).

fof(f104,plain,
    ( sK2(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_10
  <=> sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f208,plain,
    ( sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_21
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f205,f189])).

fof(f189,plain,
    ( sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1)))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f188,f53])).

fof(f53,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl6_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f188,plain,
    ( sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1)))
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f184,f57])).

fof(f57,plain,
    ( v1_funct_1(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl6_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f184,plain,
    ( ~ v1_funct_1(sK0)
    | sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1)))
    | ~ v1_relat_1(sK0)
    | ~ spl6_21 ),
    inference(resolution,[],[f176,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f176,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),sK2(k2_relat_1(sK0),sK1)),sK0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl6_21
  <=> r2_hidden(k4_tarski(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),sK2(k2_relat_1(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f205,plain,
    ( k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1))))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_23 ),
    inference(resolution,[],[f200,f91])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f90,f45])).

fof(f45,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_relat_1(sK1)
        | k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f89,f57])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK1)
        | k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f88,f53])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK1)
        | k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f87,f49])).

fof(f49,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl6_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK1)
        | k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) )
    | ~ spl6_6 ),
    inference(superposition,[],[f26,f77])).

fof(f77,plain,
    ( sK0 = k5_relat_1(sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_6
  <=> sK0 = k5_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f200,plain,
    ( r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl6_23
  <=> r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f201,plain,
    ( spl6_23
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f187,f175,f56,f52,f199])).

fof(f187,plain,
    ( r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f186,f53])).

fof(f186,plain,
    ( r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f183,f57])).

fof(f183,plain,
    ( ~ v1_funct_1(sK0)
    | r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl6_21 ),
    inference(resolution,[],[f176,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f177,plain,
    ( spl6_21
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f112,f107,f175])).

fof(f107,plain,
    ( spl6_11
  <=> sP4(sK2(k2_relat_1(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f112,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),sK2(k2_relat_1(sK0),sK1)),sK0)
    | ~ spl6_11 ),
    inference(resolution,[],[f108,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f108,plain,
    ( sP4(sK2(k2_relat_1(sK0),sK1),sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f109,plain,
    ( spl6_11
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f100,f97,f107])).

fof(f97,plain,
    ( spl6_9
  <=> r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f100,plain,
    ( sP4(sK2(k2_relat_1(sK0),sK1),sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f98,f41])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP4(X2,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f98,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f105,plain,
    ( ~ spl6_10
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f66,f48,f44,f103])).

fof(f66,plain,
    ( sK2(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f65,f17])).

fof(f17,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k2_relat_1(X0) = k1_relat_1(X1) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(f65,plain,
    ( sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f64,f19])).

fof(f19,plain,(
    sK1 != k6_relat_1(k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,
    ( sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f60,f45])).

fof(f60,plain,
    ( ~ v1_relat_1(sK1)
    | sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl6_2 ),
    inference(resolution,[],[f49,f38])).

fof(f38,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

% (30800)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f99,plain,
    ( spl6_9
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f63,f48,f44,f97])).

fof(f63,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f62,f17])).

fof(f62,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f61,f19])).

fof(f61,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f59,f45])).

fof(f59,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl6_2 ),
    inference(resolution,[],[f49,f39])).

fof(f39,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK2(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f78,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f18,f76])).

fof(f18,plain,(
    sK0 = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f21,f56])).

fof(f21,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f16,f48])).

fof(f16,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f46,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f15,f44])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:19:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (30784)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (30784)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (30801)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f78,f99,f105,f109,f177,f201,f210])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | spl6_10 | ~spl6_21 | ~spl6_23),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f209])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | spl6_10 | ~spl6_21 | ~spl6_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f208,f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    sK2(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) | spl6_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl6_10 <=> sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_21 | ~spl6_23)),
% 0.21/0.48    inference(forward_demodulation,[],[f205,f189])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1))) | (~spl6_3 | ~spl6_4 | ~spl6_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f188,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    v1_relat_1(sK0) | ~spl6_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl6_3 <=> v1_relat_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1))) | ~v1_relat_1(sK0) | (~spl6_4 | ~spl6_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f184,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    v1_funct_1(sK0) | ~spl6_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl6_4 <=> v1_funct_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1))) | ~v1_relat_1(sK0) | ~spl6_21),
% 0.21/0.48    inference(resolution,[],[f176,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),sK2(k2_relat_1(sK0),sK1)),sK0) | ~spl6_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f175])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    spl6_21 <=> r2_hidden(k4_tarski(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),sK2(k2_relat_1(sK0),sK1)),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1)))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_23)),
% 0.21/0.48    inference(resolution,[],[f200,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0))) ) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f90,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    v1_relat_1(sK1) | ~spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl6_1 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_relat_1(sK1) | k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f89,f57])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0))) ) | (~spl6_2 | ~spl6_3 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f88,f53])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0))) ) | (~spl6_2 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    v1_funct_1(sK1) | ~spl6_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl6_2 <=> v1_funct_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0))) ) | ~spl6_6),
% 0.21/0.48    inference(superposition,[],[f26,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    sK0 = k5_relat_1(sK0,sK1) | ~spl6_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl6_6 <=> sK0 = k5_relat_1(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0)) | ~spl6_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f199])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    spl6_23 <=> r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    spl6_23 | ~spl6_3 | ~spl6_4 | ~spl6_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f187,f175,f56,f52,f199])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0)) | (~spl6_3 | ~spl6_4 | ~spl6_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f186,f53])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl6_4 | ~spl6_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f183,f57])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~spl6_21),
% 0.21/0.48    inference(resolution,[],[f176,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    spl6_21 | ~spl6_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f112,f107,f175])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl6_11 <=> sP4(sK2(k2_relat_1(sK0),sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),sK2(k2_relat_1(sK0),sK1)),sK0) | ~spl6_11),
% 0.21/0.48    inference(resolution,[],[f108,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~sP4(X2,X0) | r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    sP4(sK2(k2_relat_1(sK0),sK1),sK0) | ~spl6_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f107])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl6_11 | ~spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f100,f97,f107])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl6_9 <=> r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    sP4(sK2(k2_relat_1(sK0),sK1),sK0) | ~spl6_9),
% 0.21/0.48    inference(resolution,[],[f98,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP4(X2,X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sP4(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | ~spl6_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f97])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ~spl6_10 | ~spl6_1 | ~spl6_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f66,f48,f44,f103])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    sK2(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) | (~spl6_1 | ~spl6_2)),
% 0.21/0.48    inference(forward_demodulation,[],[f65,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((k6_relat_1(k1_relat_1(X1)) != X1 & (k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1)) | (~spl6_1 | ~spl6_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    sK1 != k6_relat_1(k1_relat_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1)) | sK1 = k6_relat_1(k1_relat_1(sK1)) | (~spl6_1 | ~spl6_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f60,f45])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1)) | sK1 = k6_relat_1(k1_relat_1(sK1)) | ~spl6_2),
% 0.21/0.48    inference(resolution,[],[f49,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.48    inference(equality_resolution,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k6_relat_1(X0) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  % (30800)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl6_9 | ~spl6_1 | ~spl6_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f63,f48,f44,f97])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | (~spl6_1 | ~spl6_2)),
% 0.21/0.48    inference(forward_demodulation,[],[f62,f17])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1)) | (~spl6_1 | ~spl6_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f61,f19])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1)) | sK1 = k6_relat_1(k1_relat_1(sK1)) | (~spl6_1 | ~spl6_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f59,f45])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1)) | sK1 = k6_relat_1(k1_relat_1(sK1)) | ~spl6_2),
% 0.21/0.48    inference(resolution,[],[f49,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.49    inference(equality_resolution,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK2(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f18,f76])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    sK0 = k5_relat_1(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f56])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    v1_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f52])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f48])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f44])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (30784)------------------------------
% 0.21/0.49  % (30784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30791)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (30784)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (30784)Memory used [KB]: 6268
% 0.21/0.49  % (30784)Time elapsed: 0.069 s
% 0.21/0.49  % (30784)------------------------------
% 0.21/0.49  % (30784)------------------------------
% 0.21/0.49  % (30781)Success in time 0.124 s
%------------------------------------------------------------------------------
