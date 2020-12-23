%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0654+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:23 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 307 expanded)
%              Number of leaves         :   18 (  86 expanded)
%              Depth                    :   20
%              Number of atoms          :  507 (1510 expanded)
%              Number of equality atoms :  107 ( 490 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f415,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f205,f256,f273,f297,f332,f345,f373,f413])).

fof(f413,plain,
    ( ~ spl2_5
    | ~ spl2_6
    | spl2_8 ),
    inference(avatar_split_clause,[],[f412,f343,f254,f251])).

fof(f251,plain,
    ( spl2_5
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f254,plain,
    ( spl2_6
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f343,plain,
    ( spl2_8
  <=> v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f412,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_8 ),
    inference(subsumption_resolution,[],[f411,f36])).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))
      | k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ( k5_relat_1(k2_funct_1(X0),X0) != k6_relat_1(k2_relat_1(X0))
          | k5_relat_1(X0,k2_funct_1(X0)) != k6_relat_1(k1_relat_1(X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))
        | k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) != k6_relat_1(k2_relat_1(X0))
        | k5_relat_1(X0,k2_funct_1(X0)) != k6_relat_1(k1_relat_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) != k6_relat_1(k2_relat_1(X0))
        | k5_relat_1(X0,k2_funct_1(X0)) != k6_relat_1(k1_relat_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
            & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f411,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_8 ),
    inference(subsumption_resolution,[],[f408,f37])).

fof(f37,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f408,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_8 ),
    inference(resolution,[],[f344,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f344,plain,
    ( ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f343])).

fof(f373,plain,
    ( ~ spl2_5
    | ~ spl2_6
    | spl2_7 ),
    inference(avatar_split_clause,[],[f372,f340,f254,f251])).

fof(f340,plain,
    ( spl2_7
  <=> v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f372,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_7 ),
    inference(subsumption_resolution,[],[f371,f36])).

fof(f371,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_7 ),
    inference(subsumption_resolution,[],[f369,f37])).

fof(f369,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_7 ),
    inference(resolution,[],[f341,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f341,plain,
    ( ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f340])).

fof(f345,plain,
    ( ~ spl2_7
    | ~ spl2_8
    | spl2_2 ),
    inference(avatar_split_clause,[],[f338,f65,f343,f340])).

fof(f65,plain,
    ( spl2_2
  <=> k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f338,plain,
    ( ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f337,f36])).

fof(f337,plain,
    ( ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(sK0)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f336,f37])).

fof(f336,plain,
    ( ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f335,f38])).

fof(f38,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f335,plain,
    ( ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_2 ),
    inference(trivial_inequality_removal,[],[f334])).

fof(f334,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_2 ),
    inference(superposition,[],[f66,f178])).

fof(f178,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v1_funct_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f177,f70])).

fof(f70,plain,(
    ! [X2] :
      ( r2_hidden(sK1(k2_relat_1(X2),k5_relat_1(k2_funct_1(X2),X2)),k2_relat_1(X2))
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(k2_relat_1(X2))
      | ~ v1_funct_1(k5_relat_1(k2_funct_1(X2),X2))
      | ~ v1_relat_1(k5_relat_1(k2_funct_1(X2),X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f58,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f58,plain,(
    ! [X1] :
      ( r2_hidden(sK1(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK1(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK1(X0,X1) != k1_funct_1(X1,sK1(X0,X1))
            & r2_hidden(sK1(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

% (29402)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f177,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k2_relat_1(X0),k5_relat_1(k2_funct_1(X0),X0)),k2_relat_1(X0))
      | ~ v1_funct_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v1_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k2_relat_1(X0),k5_relat_1(k2_funct_1(X0),X0)),k2_relat_1(X0))
      | ~ v1_funct_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v1_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f98,f44])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)),k5_relat_1(k2_funct_1(X0),X0)),k2_relat_1(X0))
      | ~ v1_funct_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v1_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( sK1(k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)),k5_relat_1(k2_funct_1(X0),X0)) != sK1(k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)),k5_relat_1(k2_funct_1(X0),X0))
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))
      | ~ v1_funct_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v1_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ r2_hidden(sK1(k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)),k5_relat_1(k2_funct_1(X0),X0)),k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f57,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(f57,plain,(
    ! [X1] :
      ( sK1(k1_relat_1(X1),X1) != k1_funct_1(X1,sK1(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK1(X0,X1) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f332,plain,
    ( ~ spl2_5
    | ~ spl2_6
    | spl2_4 ),
    inference(avatar_split_clause,[],[f331,f203,f254,f251])).

fof(f203,plain,
    ( spl2_4
  <=> v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f331,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_4 ),
    inference(subsumption_resolution,[],[f330,f36])).

fof(f330,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl2_4 ),
    inference(subsumption_resolution,[],[f327,f37])).

fof(f327,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_4 ),
    inference(resolution,[],[f204,f46])).

fof(f204,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f203])).

fof(f297,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | spl2_6 ),
    inference(subsumption_resolution,[],[f295,f36])).

fof(f295,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_6 ),
    inference(subsumption_resolution,[],[f294,f37])).

fof(f294,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_6 ),
    inference(resolution,[],[f255,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f255,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f254])).

fof(f273,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f271,f36])).

fof(f271,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_5 ),
    inference(subsumption_resolution,[],[f270,f37])).

fof(f270,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_5 ),
    inference(resolution,[],[f252,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f252,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f251])).

fof(f256,plain,
    ( ~ spl2_5
    | ~ spl2_6
    | spl2_3 ),
    inference(avatar_split_clause,[],[f249,f200,f254,f251])).

fof(f200,plain,
    ( spl2_3
  <=> v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f249,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_3 ),
    inference(subsumption_resolution,[],[f248,f36])).

fof(f248,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl2_3 ),
    inference(subsumption_resolution,[],[f246,f37])).

fof(f246,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_3 ),
    inference(resolution,[],[f201,f47])).

fof(f201,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f200])).

fof(f205,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f198,f62,f203,f200])).

fof(f62,plain,
    ( spl2_1
  <=> k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f198,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f197,f36])).

fof(f197,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f196,f37])).

fof(f196,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f195,f38])).

fof(f195,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_1 ),
    inference(trivial_inequality_removal,[],[f179])).

fof(f179,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_1 ),
    inference(superposition,[],[f63,f173])).

fof(f173,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f172,f69])).

fof(f69,plain,(
    ! [X1] :
      ( r2_hidden(sK1(k1_relat_1(X1),k5_relat_1(X1,k2_funct_1(X1))),k1_relat_1(X1))
      | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
      | ~ v1_funct_1(k5_relat_1(X1,k2_funct_1(X1)))
      | ~ v1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f58,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f172,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k1_relat_1(X0),k5_relat_1(X0,k2_funct_1(X0))),k1_relat_1(X0))
      | ~ v1_funct_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k1_relat_1(X0),k5_relat_1(X0,k2_funct_1(X0))),k1_relat_1(X0))
      | ~ v1_funct_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f97,f42])).

fof(f97,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))),k5_relat_1(X1,k2_funct_1(X1))),k1_relat_1(X1))
      | ~ v1_funct_1(k5_relat_1(X1,k2_funct_1(X1)))
      | ~ v1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))
      | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(trivial_inequality_removal,[],[f93])).

fof(f93,plain,(
    ! [X1] :
      ( sK1(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))),k5_relat_1(X1,k2_funct_1(X1))) != sK1(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))),k5_relat_1(X1,k2_funct_1(X1)))
      | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))))
      | ~ v1_funct_1(k5_relat_1(X1,k2_funct_1(X1)))
      | ~ v1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))
      | ~ r2_hidden(sK1(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))),k5_relat_1(X1,k2_funct_1(X1))),k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f57,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f63,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f67,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f39,f65,f62])).

fof(f39,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))
    | k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

%------------------------------------------------------------------------------
