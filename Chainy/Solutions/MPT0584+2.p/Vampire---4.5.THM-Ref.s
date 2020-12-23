%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0584+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:38 EST 2020

% Result     : Theorem 2.45s
% Output     : Refutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   39 (  82 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  118 ( 340 expanded)
%              Number of equality atoms :   36 ( 130 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2351,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2045,f2050,f2055,f2065,f2075,f2350])).

fof(f2350,plain,
    ( ~ spl93_1
    | ~ spl93_2
    | ~ spl93_3
    | ~ spl93_5
    | spl93_7 ),
    inference(avatar_contradiction_clause,[],[f2349])).

fof(f2349,plain,
    ( $false
    | ~ spl93_1
    | ~ spl93_2
    | ~ spl93_3
    | ~ spl93_5
    | spl93_7 ),
    inference(subsumption_resolution,[],[f2348,f2074])).

fof(f2074,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    | spl93_7 ),
    inference(avatar_component_clause,[],[f2072])).

fof(f2072,plain,
    ( spl93_7
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_7])])).

fof(f2348,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl93_1
    | ~ spl93_2
    | ~ spl93_3
    | ~ spl93_5 ),
    inference(backward_demodulation,[],[f2347,f2317])).

fof(f2317,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2)
    | ~ spl93_1
    | ~ spl93_3 ),
    inference(unit_resulting_resolution,[],[f2044,f2054,f1356])).

fof(f1356,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f857])).

fof(f857,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f856])).

fof(f856,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f693])).

fof(f693,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f2054,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl93_3 ),
    inference(avatar_component_clause,[],[f2052])).

fof(f2052,plain,
    ( spl93_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_3])])).

fof(f2044,plain,
    ( v1_relat_1(sK0)
    | ~ spl93_1 ),
    inference(avatar_component_clause,[],[f2042])).

fof(f2042,plain,
    ( spl93_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_1])])).

fof(f2347,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(k7_relat_1(sK0,sK3),sK2)
    | ~ spl93_2
    | ~ spl93_3
    | ~ spl93_5 ),
    inference(forward_demodulation,[],[f2318,f2064])).

fof(f2064,plain,
    ( k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    | ~ spl93_5 ),
    inference(avatar_component_clause,[],[f2062])).

fof(f2062,plain,
    ( spl93_5
  <=> k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_5])])).

fof(f2318,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(k7_relat_1(sK1,sK3),sK2)
    | ~ spl93_2
    | ~ spl93_3 ),
    inference(unit_resulting_resolution,[],[f2049,f2054,f1356])).

fof(f2049,plain,
    ( v1_relat_1(sK1)
    | ~ spl93_2 ),
    inference(avatar_component_clause,[],[f2047])).

fof(f2047,plain,
    ( spl93_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_2])])).

fof(f2075,plain,(
    ~ spl93_7 ),
    inference(avatar_split_clause,[],[f1350,f2072])).

fof(f1350,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f1144])).

fof(f1144,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f850,f1143,f1142,f1141])).

fof(f1141,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
              & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1142,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
            & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3)
            & r1_tarski(X2,X3) )
        & v1_relat_1(X1) )
   => ( ? [X3,X2] :
          ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
          & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
          & r1_tarski(X2,X3) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1143,plain,
    ( ? [X3,X2] :
        ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
        & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
        & r1_tarski(X2,X3) )
   => ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
      & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f850,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f849])).

fof(f849,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f776])).

fof(f776,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2,X3] :
                ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                  & r1_tarski(X2,X3) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f775])).

fof(f775,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t188_relat_1)).

fof(f2065,plain,(
    spl93_5 ),
    inference(avatar_split_clause,[],[f1349,f2062])).

fof(f1349,plain,(
    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f1144])).

fof(f2055,plain,(
    spl93_3 ),
    inference(avatar_split_clause,[],[f1348,f2052])).

fof(f1348,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f1144])).

fof(f2050,plain,(
    spl93_2 ),
    inference(avatar_split_clause,[],[f1347,f2047])).

fof(f1347,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1144])).

fof(f2045,plain,(
    spl93_1 ),
    inference(avatar_split_clause,[],[f1346,f2042])).

fof(f1346,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1144])).
%------------------------------------------------------------------------------
