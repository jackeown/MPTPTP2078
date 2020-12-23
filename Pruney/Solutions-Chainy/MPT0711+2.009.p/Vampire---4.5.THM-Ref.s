%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 235 expanded)
%              Number of leaves         :   23 ( 104 expanded)
%              Depth                    :    9
%              Number of atoms          :  372 (1078 expanded)
%              Number of equality atoms :   96 ( 344 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f507,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f71,f92,f106,f172,f243,f463,f479,f485,f506])).

fof(f506,plain,
    ( spl4_34
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f503,f465,f482])).

fof(f482,plain,
    ( spl4_34
  <=> k1_funct_1(sK1,sK3(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK0,sK3(k7_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f465,plain,
    ( spl4_32
  <=> r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f503,plain,
    ( k1_funct_1(sK1,sK3(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK0,sK3(k7_relat_1(sK0,sK2),sK1))
    | ~ spl4_32 ),
    inference(resolution,[],[f467,f31])).

fof(f31,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & ! [X3] :
        ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK2) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(sK0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
            & ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(X1) = k1_relat_1(sK0) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
          & ! [X3] :
              ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(sK0) = k1_relat_1(sK1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
        & ! [X3] :
            ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
            | ~ r2_hidden(X3,X2) )
        & k1_relat_1(sK0) = k1_relat_1(sK1) )
   => ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
      & ! [X3] :
          ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
          | ~ r2_hidden(X3,sK2) )
      & k1_relat_1(sK0) = k1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
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
           => ! [X2] :
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X1,X3) = k1_funct_1(X0,X3) )
                  & k1_relat_1(X1) = k1_relat_1(X0) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X1,X3) = k1_funct_1(X0,X3) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).

fof(f467,plain,
    ( r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),sK2)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f465])).

fof(f485,plain,
    ( ~ spl4_34
    | spl4_24
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f480,f460,f240,f482])).

fof(f240,plain,
    ( spl4_24
  <=> k1_funct_1(k7_relat_1(sK0,sK2),sK3(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK1,sK3(k7_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f460,plain,
    ( spl4_31
  <=> k1_funct_1(k7_relat_1(sK0,sK2),sK3(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK0,sK3(k7_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f480,plain,
    ( k1_funct_1(sK1,sK3(k7_relat_1(sK0,sK2),sK1)) != k1_funct_1(sK0,sK3(k7_relat_1(sK0,sK2),sK1))
    | spl4_24
    | ~ spl4_31 ),
    inference(backward_demodulation,[],[f242,f462])).

fof(f462,plain,
    ( k1_funct_1(k7_relat_1(sK0,sK2),sK3(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK0,sK3(k7_relat_1(sK0,sK2),sK1))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f460])).

fof(f242,plain,
    ( k1_funct_1(k7_relat_1(sK0,sK2),sK3(k7_relat_1(sK0,sK2),sK1)) != k1_funct_1(sK1,sK3(k7_relat_1(sK0,sK2),sK1))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f240])).

fof(f479,plain,
    ( ~ spl4_6
    | spl4_32
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f457,f169,f465,f68])).

fof(f68,plain,
    ( spl4_6
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f169,plain,
    ( spl4_15
  <=> r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),k3_xboole_0(k1_relat_1(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f457,plain,
    ( r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl4_15 ),
    inference(resolution,[],[f171,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(k1_relat_1(X0),X1))
      | r2_hidden(X2,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(k1_relat_1(X0),X1))
      | r2_hidden(X2,X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f34,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f171,plain,
    ( r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),k3_xboole_0(k1_relat_1(sK0),sK2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f463,plain,
    ( spl4_31
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f453,f169,f68,f63,f460])).

fof(f63,plain,
    ( spl4_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f453,plain,
    ( k1_funct_1(k7_relat_1(sK0,sK2),sK3(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK0,sK3(k7_relat_1(sK0,sK2),sK1))
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f70,f65,f171,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

fof(f65,plain,
    ( v1_funct_1(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f70,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f243,plain,
    ( ~ spl4_24
    | spl4_1
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f236,f104,f68,f63,f43,f240])).

% (28127)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
fof(f43,plain,
    ( spl4_1
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f104,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK0),X1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k7_relat_1(sK1,X1) = X0
        | k1_funct_1(X0,sK3(X0,sK1)) != k1_funct_1(sK1,sK3(X0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f236,plain,
    ( k1_funct_1(k7_relat_1(sK0,sK2),sK3(k7_relat_1(sK0,sK2),sK1)) != k1_funct_1(sK1,sK3(k7_relat_1(sK0,sK2),sK1))
    | spl4_1
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f73,f75,f45,f77,f105])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(X0,sK3(X0,sK1)) != k1_funct_1(sK1,sK3(X0,sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k7_relat_1(sK1,X1) = X0
        | k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK0),X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f77,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f70,f41])).

fof(f45,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f75,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK0,X0))
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f70,f65,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f73,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK0,X0))
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f70,f65,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f172,plain,
    ( spl4_15
    | spl4_1
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f167,f90,f68,f63,f43,f169])).

fof(f90,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK0),X1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k7_relat_1(sK1,X1) = X0
        | r2_hidden(sK3(X0,sK1),k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f167,plain,
    ( r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),k3_xboole_0(k1_relat_1(sK0),sK2))
    | spl4_1
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f161,f77])).

fof(f161,plain,
    ( r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),k1_relat_1(k7_relat_1(sK0,sK2)))
    | spl4_1
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f73,f75,f45,f77,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK0),X1)
        | k7_relat_1(sK1,X1) = X0
        | r2_hidden(sK3(X0,sK1),k1_relat_1(X0)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f106,plain,
    ( ~ spl4_4
    | spl4_9
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f102,f53,f48,f104,f58])).

fof(f58,plain,
    ( spl4_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f48,plain,
    ( spl4_2
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f53,plain,
    ( spl4_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK0),X1)
        | k1_funct_1(X0,sK3(X0,sK1)) != k1_funct_1(sK1,sK3(X0,sK1))
        | k7_relat_1(sK1,X1) = X0
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f99,f50])).

fof(f50,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(X0,sK3(X0,sK1)) != k1_funct_1(sK1,sK3(X0,sK1))
        | k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK1),X1)
        | k7_relat_1(sK1,X1) = X0
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f38,f55])).

fof(f55,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2))
      | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | k7_relat_1(X2,X0) = X1
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ( k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2))
            & r2_hidden(sK3(X1,X2),k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f24])).

fof(f24,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2))
        & r2_hidden(sK3(X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0) )
           => k7_relat_1(X2,X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).

fof(f92,plain,
    ( ~ spl4_4
    | spl4_7
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f88,f53,f48,f90,f58])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK0),X1)
        | r2_hidden(sK3(X0,sK1),k1_relat_1(X0))
        | k7_relat_1(sK1,X1) = X0
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f85,f50])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,sK1),k1_relat_1(X0))
        | k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK1),X1)
        | k7_relat_1(sK1,X1) = X0
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f37,f55])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | r2_hidden(sK3(X1,X2),k1_relat_1(X1))
      | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | k7_relat_1(X2,X0) = X1
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f26,f68])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f30,f48])).

fof(f30,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f32,f43])).

fof(f32,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:08:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (28136)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.46  % (28126)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.48  % (28129)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (28130)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.48  % (28123)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (28131)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.49  % (28139)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.49  % (28119)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (28120)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (28120)Refutation not found, incomplete strategy% (28120)------------------------------
% 0.21/0.49  % (28120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28120)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (28120)Memory used [KB]: 10618
% 0.21/0.49  % (28120)Time elapsed: 0.086 s
% 0.21/0.49  % (28120)------------------------------
% 0.21/0.49  % (28120)------------------------------
% 0.21/0.49  % (28135)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.49  % (28121)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (28133)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.49  % (28122)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (28132)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (28134)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.50  % (28118)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (28128)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (28125)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (28137)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (28138)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (28117)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (28123)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f507,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f71,f92,f106,f172,f243,f463,f479,f485,f506])).
% 0.21/0.51  fof(f506,plain,(
% 0.21/0.51    spl4_34 | ~spl4_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f503,f465,f482])).
% 0.21/0.51  fof(f482,plain,(
% 0.21/0.51    spl4_34 <=> k1_funct_1(sK1,sK3(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK0,sK3(k7_relat_1(sK0,sK2),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.51  fof(f465,plain,(
% 0.21/0.51    spl4_32 <=> r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.51  fof(f503,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK3(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK0,sK3(k7_relat_1(sK0,sK2),sK1)) | ~spl4_32),
% 0.21/0.51    inference(resolution,[],[f467,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f20,f19,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X1,X3) = k1_funct_1(X0,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X1,X3) = k1_funct_1(X0,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).
% 0.21/0.51  fof(f467,plain,(
% 0.21/0.51    r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),sK2) | ~spl4_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f465])).
% 0.21/0.51  fof(f485,plain,(
% 0.21/0.51    ~spl4_34 | spl4_24 | ~spl4_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f480,f460,f240,f482])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    spl4_24 <=> k1_funct_1(k7_relat_1(sK0,sK2),sK3(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK1,sK3(k7_relat_1(sK0,sK2),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.51  fof(f460,plain,(
% 0.21/0.51    spl4_31 <=> k1_funct_1(k7_relat_1(sK0,sK2),sK3(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK0,sK3(k7_relat_1(sK0,sK2),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.51  fof(f480,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK3(k7_relat_1(sK0,sK2),sK1)) != k1_funct_1(sK0,sK3(k7_relat_1(sK0,sK2),sK1)) | (spl4_24 | ~spl4_31)),
% 0.21/0.51    inference(backward_demodulation,[],[f242,f462])).
% 0.21/0.51  fof(f462,plain,(
% 0.21/0.51    k1_funct_1(k7_relat_1(sK0,sK2),sK3(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK0,sK3(k7_relat_1(sK0,sK2),sK1)) | ~spl4_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f460])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    k1_funct_1(k7_relat_1(sK0,sK2),sK3(k7_relat_1(sK0,sK2),sK1)) != k1_funct_1(sK1,sK3(k7_relat_1(sK0,sK2),sK1)) | spl4_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f240])).
% 0.21/0.51  fof(f479,plain,(
% 0.21/0.51    ~spl4_6 | spl4_32 | ~spl4_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f457,f169,f465,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl4_6 <=> v1_relat_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl4_15 <=> r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),k3_xboole_0(k1_relat_1(sK0),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.51  fof(f457,plain,(
% 0.21/0.51    r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),sK2) | ~v1_relat_1(sK0) | ~spl4_15),
% 0.21/0.51    inference(resolution,[],[f171,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(k1_relat_1(X0),X1)) | r2_hidden(X2,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(k1_relat_1(X0),X1)) | r2_hidden(X2,X1) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(superposition,[],[f34,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),k3_xboole_0(k1_relat_1(sK0),sK2)) | ~spl4_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f169])).
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    spl4_31 | ~spl4_5 | ~spl4_6 | ~spl4_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f453,f169,f68,f63,f460])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    spl4_5 <=> v1_funct_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f453,plain,(
% 0.21/0.51    k1_funct_1(k7_relat_1(sK0,sK2),sK3(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK0,sK3(k7_relat_1(sK0,sK2),sK1)) | (~spl4_5 | ~spl4_6 | ~spl4_15)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f70,f65,f171,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    v1_funct_1(sK0) | ~spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f63])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    v1_relat_1(sK0) | ~spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f68])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    ~spl4_24 | spl4_1 | ~spl4_5 | ~spl4_6 | ~spl4_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f236,f104,f68,f63,f43,f240])).
% 0.21/0.51  % (28127)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    spl4_1 <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl4_9 <=> ! [X1,X0] : (k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK0),X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k7_relat_1(sK1,X1) = X0 | k1_funct_1(X0,sK3(X0,sK1)) != k1_funct_1(sK1,sK3(X0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    k1_funct_1(k7_relat_1(sK0,sK2),sK3(k7_relat_1(sK0,sK2),sK1)) != k1_funct_1(sK1,sK3(k7_relat_1(sK0,sK2),sK1)) | (spl4_1 | ~spl4_5 | ~spl4_6 | ~spl4_9)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f73,f75,f45,f77,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_funct_1(X0,sK3(X0,sK1)) != k1_funct_1(sK1,sK3(X0,sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k7_relat_1(sK1,X1) = X0 | k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK0),X1)) ) | ~spl4_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f104])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)) ) | ~spl4_6),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f70,f41])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) | spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f43])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0))) ) | (~spl4_5 | ~spl4_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f70,f65,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k7_relat_1(sK0,X0))) ) | (~spl4_5 | ~spl4_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f70,f65,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    spl4_15 | spl4_1 | ~spl4_5 | ~spl4_6 | ~spl4_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f167,f90,f68,f63,f43,f169])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl4_7 <=> ! [X1,X0] : (k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK0),X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k7_relat_1(sK1,X1) = X0 | r2_hidden(sK3(X0,sK1),k1_relat_1(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),k3_xboole_0(k1_relat_1(sK0),sK2)) | (spl4_1 | ~spl4_5 | ~spl4_6 | ~spl4_7)),
% 0.21/0.51    inference(forward_demodulation,[],[f161,f77])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    r2_hidden(sK3(k7_relat_1(sK0,sK2),sK1),k1_relat_1(k7_relat_1(sK0,sK2))) | (spl4_1 | ~spl4_5 | ~spl4_6 | ~spl4_7)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f73,f75,f45,f77,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK0),X1) | k7_relat_1(sK1,X1) = X0 | r2_hidden(sK3(X0,sK1),k1_relat_1(X0))) ) | ~spl4_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ~spl4_4 | spl4_9 | ~spl4_2 | ~spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f102,f53,f48,f104,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl4_4 <=> v1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    spl4_2 <=> k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    spl4_3 <=> v1_funct_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK0),X1) | k1_funct_1(X0,sK3(X0,sK1)) != k1_funct_1(sK1,sK3(X0,sK1)) | k7_relat_1(sK1,X1) = X0 | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.51    inference(forward_demodulation,[],[f99,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k1_relat_1(sK1) | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f48])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_funct_1(X0,sK3(X0,sK1)) != k1_funct_1(sK1,sK3(X0,sK1)) | k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK1),X1) | k7_relat_1(sK1,X1) = X0 | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl4_3),
% 0.21/0.51    inference(resolution,[],[f38,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    v1_funct_1(sK1) | ~spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f53])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2)) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | k7_relat_1(X2,X0) = X1 | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | (k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2)) & r2_hidden(sK3(X1,X2),k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X2,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2)) & r2_hidden(sK3(X1,X2),k1_relat_1(X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | ? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((k7_relat_1(X2,X0) = X1 | (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)) => k7_relat_1(X2,X0) = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~spl4_4 | spl4_7 | ~spl4_2 | ~spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f88,f53,f48,f90,f58])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK0),X1) | r2_hidden(sK3(X0,sK1),k1_relat_1(X0)) | k7_relat_1(sK1,X1) = X0 | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.51    inference(forward_demodulation,[],[f85,f50])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,sK1),k1_relat_1(X0)) | k1_relat_1(X0) != k3_xboole_0(k1_relat_1(sK1),X1) | k7_relat_1(sK1,X1) = X0 | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl4_3),
% 0.21/0.51    inference(resolution,[],[f37,f55])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | r2_hidden(sK3(X1,X2),k1_relat_1(X1)) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | k7_relat_1(X2,X0) = X1 | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f68])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f27,f63])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    v1_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f58])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f53])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f48])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ~spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f43])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (28123)------------------------------
% 0.21/0.51  % (28123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28123)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (28123)Memory used [KB]: 11129
% 0.21/0.51  % (28123)Time elapsed: 0.062 s
% 0.21/0.51  % (28123)------------------------------
% 0.21/0.51  % (28123)------------------------------
% 0.21/0.51  % (28124)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (28116)Success in time 0.16 s
%------------------------------------------------------------------------------
