%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:42 EST 2020

% Result     : Theorem 10.38s
% Output     : Refutation 10.38s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 624 expanded)
%              Number of leaves         :   42 ( 253 expanded)
%              Depth                    :   11
%              Number of atoms          :  800 (2733 expanded)
%              Number of equality atoms :   89 ( 505 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9681,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f177,f185,f222,f223,f224,f225,f226,f245,f299,f471,f476,f599,f673,f737,f1362,f2052,f2065,f2190,f6272,f6282,f9355,f9358,f9359,f9361,f9417,f9419,f9435,f9474,f9650,f9660,f9661,f9673])).

fof(f9673,plain,
    ( ~ spl16_38
    | ~ spl16_8 ),
    inference(avatar_split_clause,[],[f1182,f208,f541])).

fof(f541,plain,
    ( spl16_38
  <=> r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_38])])).

fof(f208,plain,
    ( spl16_8
  <=> r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).

fof(f1182,plain,
    ( ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | ~ spl16_8 ),
    inference(resolution,[],[f209,f120])).

fof(f120,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f103,f79])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK14(X0,X1,X2),X1)
            | ~ r2_hidden(sK14(X0,X1,X2),X0)
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
              & r2_hidden(sK14(X0,X1,X2),X0) )
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f63,f64])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK14(X0,X1,X2),X1)
          | ~ r2_hidden(sK14(X0,X1,X2),X0)
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
            & r2_hidden(sK14(X0,X1,X2),X0) )
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f209,plain,
    ( r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | ~ spl16_8 ),
    inference(avatar_component_clause,[],[f208])).

fof(f9661,plain,
    ( spl16_32
    | ~ spl16_37 ),
    inference(avatar_split_clause,[],[f6369,f537,f473])).

fof(f473,plain,
    ( spl16_32
  <=> r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_32])])).

fof(f537,plain,
    ( spl16_37
  <=> r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_37])])).

fof(f6369,plain,
    ( r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK2)
    | ~ spl16_37 ),
    inference(resolution,[],[f1822,f142])).

fof(f142,plain,(
    ! [X1] : r1_tarski(k7_relat_1(sK2,X1),sK2) ),
    inference(resolution,[],[f66,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f66,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

fof(f1822,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),X3)
        | r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),X3) )
    | ~ spl16_37 ),
    inference(resolution,[],[f538,f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK13(X0,X1),X1)
          & r2_hidden(sK13(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK13(X0,X1),X1)
        & r2_hidden(sK13(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f538,plain,
    ( r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0))
    | ~ spl16_37 ),
    inference(avatar_component_clause,[],[f537])).

fof(f9660,plain,
    ( ~ spl16_1
    | ~ spl16_30
    | ~ spl16_31
    | ~ spl16_32
    | spl16_7 ),
    inference(avatar_split_clause,[],[f1169,f204,f473,f468,f464,f171])).

fof(f171,plain,
    ( spl16_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f464,plain,
    ( spl16_30
  <=> v1_relat_1(k7_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_30])])).

fof(f468,plain,
    ( spl16_31
  <=> r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_31])])).

fof(f204,plain,
    ( spl16_7
  <=> r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_7])])).

fof(f1169,plain,
    ( ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK2)
    | ~ r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | spl16_7 ),
    inference(resolution,[],[f206,f116])).

fof(f116,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK3(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                    & r2_hidden(sK3(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f206,plain,
    ( ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | spl16_7 ),
    inference(avatar_component_clause,[],[f204])).

fof(f9650,plain,
    ( ~ spl16_394
    | spl16_314
    | spl16_31 ),
    inference(avatar_split_clause,[],[f9644,f468,f6279,f9421])).

fof(f9421,plain,
    ( spl16_394
  <=> r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_394])])).

fof(f6279,plain,
    ( spl16_314
  <=> r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_314])])).

fof(f9644,plain,
    ( r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK1)
    | ~ r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK0)
    | spl16_31 ),
    inference(resolution,[],[f469,f119])).

fof(f119,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f104,f79])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f469,plain,
    ( ~ r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(sK0,sK1))
    | spl16_31 ),
    inference(avatar_component_clause,[],[f468])).

fof(f9474,plain,
    ( ~ spl16_6
    | ~ spl16_54 ),
    inference(avatar_contradiction_clause,[],[f9453])).

fof(f9453,plain,
    ( $false
    | ~ spl16_6
    | ~ spl16_54 ),
    inference(resolution,[],[f202,f736])).

fof(f736,plain,
    ( sQ15_eqProxy(k4_tarski(sK6(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK7(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))
    | ~ spl16_54 ),
    inference(avatar_component_clause,[],[f734])).

fof(f734,plain,
    ( spl16_54
  <=> sQ15_eqProxy(k4_tarski(sK6(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK7(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_54])])).

fof(f202,plain,
    ( ! [X0,X1] : ~ sQ15_eqProxy(k4_tarski(X0,X1),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))
    | ~ spl16_6 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl16_6
  <=> ! [X1,X0] : ~ sQ15_eqProxy(k4_tarski(X0,X1),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f9435,plain,
    ( ~ spl16_1
    | ~ spl16_128
    | spl16_394
    | ~ spl16_37 ),
    inference(avatar_split_clause,[],[f1817,f537,f9421,f1698,f171])).

fof(f1698,plain,
    ( spl16_128
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_128])])).

fof(f1817,plain,
    ( r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl16_37 ),
    inference(resolution,[],[f538,f118])).

fof(f118,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9419,plain,
    ( ~ spl16_1
    | ~ spl16_132
    | ~ spl16_314
    | ~ spl16_32
    | spl16_38 ),
    inference(avatar_split_clause,[],[f2192,f541,f473,f6279,f1744,f171])).

fof(f1744,plain,
    ( spl16_132
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_132])])).

fof(f2192,plain,
    ( ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK2)
    | ~ r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | spl16_38 ),
    inference(resolution,[],[f542,f116])).

fof(f542,plain,
    ( ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))
    | spl16_38 ),
    inference(avatar_component_clause,[],[f541])).

fof(f9417,plain,
    ( ~ spl16_5
    | ~ spl16_107 ),
    inference(avatar_contradiction_clause,[],[f9400])).

fof(f9400,plain,
    ( $false
    | ~ spl16_5
    | ~ spl16_107 ),
    inference(resolution,[],[f199,f1361])).

fof(f1361,plain,
    ( sQ15_eqProxy(k4_tarski(sK6(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK7(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))
    | ~ spl16_107 ),
    inference(avatar_component_clause,[],[f1359])).

fof(f1359,plain,
    ( spl16_107
  <=> sQ15_eqProxy(k4_tarski(sK6(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK7(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_107])])).

fof(f199,plain,
    ( ! [X2,X3] : ~ sQ15_eqProxy(k4_tarski(X2,X3),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))
    | ~ spl16_5 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl16_5
  <=> ! [X3,X2] : ~ sQ15_eqProxy(k4_tarski(X2,X3),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f9361,plain,
    ( ~ spl16_8
    | ~ spl16_7
    | spl16_10
    | ~ spl16_151 ),
    inference(avatar_split_clause,[],[f6563,f2183,f218,f204,f208])).

fof(f218,plain,
    ( spl16_10
  <=> r2_hidden(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f2183,plain,
    ( spl16_151
  <=> ! [X4] :
        ( sQ15_eqProxy(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)
        | r2_hidden(sK11(X4),X4)
        | ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
        | ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_151])])).

fof(f6563,plain,
    ( r2_hidden(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | ~ spl16_151 ),
    inference(resolution,[],[f2184,f123])).

fof(f123,plain,(
    ~ sQ15_eqProxy(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) ),
    inference(equality_proxy_replacement,[],[f67,f122])).

fof(f122,plain,(
    ! [X1,X0] :
      ( sQ15_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ15_eqProxy])])).

fof(f67,plain,(
    k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f2184,plain,
    ( ! [X4] :
        ( sQ15_eqProxy(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)
        | r2_hidden(sK11(X4),X4)
        | ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
        | ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)),X4) )
    | ~ spl16_151 ),
    inference(avatar_component_clause,[],[f2183])).

fof(f9359,plain,
    ( spl16_9
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_54 ),
    inference(avatar_split_clause,[],[f6844,f734,f208,f204,f213])).

fof(f213,plain,
    ( spl16_9
  <=> r2_hidden(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).

fof(f6844,plain,
    ( ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | r2_hidden(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ spl16_54 ),
    inference(resolution,[],[f1482,f123])).

fof(f1482,plain,
    ( ! [X4] :
        ( sQ15_eqProxy(X4,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
        | ~ r2_hidden(k4_tarski(sK9(X4,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(X4,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
        | ~ r2_hidden(k4_tarski(sK9(X4,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(X4,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),X4)
        | r2_hidden(sK12(X4),X4) )
    | ~ spl16_54 ),
    inference(resolution,[],[f736,f130])).

fof(f130,plain,(
    ! [X6,X0,X5,X1] :
      ( sQ15_eqProxy(X0,X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | ~ sQ15_eqProxy(k4_tarski(X5,X6),sK11(X1))
      | r2_hidden(sK12(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f93,f122,f122])).

fof(f93,plain,(
    ! [X6,X0,X5,X1] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK11(X1)
      | r2_hidden(sK12(X0),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) ) )
      | ( ! [X5,X6] : k4_tarski(X5,X6) != sK11(X1)
        & r2_hidden(sK11(X1),X1) )
      | ( ! [X8,X9] : k4_tarski(X8,X9) != sK12(X0)
        & r2_hidden(sK12(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f51,f54,f53,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X1] :
      ( ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
     => ( ! [X6,X5] : k4_tarski(X5,X6) != sK11(X1)
        & r2_hidden(sK11(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) )
     => ( ! [X9,X8] : k4_tarski(X8,X9) != sK12(X0)
        & r2_hidden(sK12(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X0)
        <~> r2_hidden(k4_tarski(X2,X3),X1) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X0)
        <~> r2_hidden(k4_tarski(X2,X3),X1) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X0)
          <=> r2_hidden(k4_tarski(X2,X3),X1) )
        & ! [X4] :
            ~ ( ! [X5,X6] : k4_tarski(X5,X6) != X4
              & r2_hidden(X4,X1) )
        & ! [X7] :
            ~ ( ! [X8,X9] : k4_tarski(X8,X9) != X7
              & r2_hidden(X7,X0) ) )
     => X0 = X1 ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X0)
          <=> r2_hidden(k4_tarski(X2,X3),X1) )
        & ! [X2] :
            ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X2
              & r2_hidden(X2,X1) )
        & ! [X2] :
            ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X2
              & r2_hidden(X2,X0) ) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l131_zfmisc_1)).

fof(f9358,plain,
    ( spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_54 ),
    inference(avatar_split_clause,[],[f6965,f734,f208,f204,f198])).

fof(f6965,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
        | ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
        | ~ sQ15_eqProxy(k4_tarski(X0,X1),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))) )
    | ~ spl16_54 ),
    inference(resolution,[],[f1483,f123])).

fof(f1483,plain,
    ( ! [X6,X7,X5] :
        ( sQ15_eqProxy(X5,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
        | ~ r2_hidden(k4_tarski(sK9(X5,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(X5,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
        | ~ r2_hidden(k4_tarski(sK9(X5,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(X5,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),X5)
        | ~ sQ15_eqProxy(k4_tarski(X6,X7),sK12(X5)) )
    | ~ spl16_54 ),
    inference(resolution,[],[f736,f129])).

fof(f129,plain,(
    ! [X6,X0,X8,X5,X1,X9] :
      ( sQ15_eqProxy(X0,X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | ~ sQ15_eqProxy(k4_tarski(X5,X6),sK11(X1))
      | ~ sQ15_eqProxy(k4_tarski(X8,X9),sK12(X0)) ) ),
    inference(equality_proxy_replacement,[],[f94,f122,f122,f122])).

fof(f94,plain,(
    ! [X6,X0,X8,X5,X1,X9] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK11(X1)
      | k4_tarski(X8,X9) != sK12(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f9355,plain,
    ( ~ spl16_31
    | ~ spl16_314 ),
    inference(avatar_contradiction_clause,[],[f9343])).

fof(f9343,plain,
    ( $false
    | ~ spl16_31
    | ~ spl16_314 ),
    inference(resolution,[],[f6281,f1133])).

fof(f1133,plain,
    ( ~ r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK1)
    | ~ spl16_31 ),
    inference(resolution,[],[f470,f120])).

fof(f470,plain,
    ( r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(sK0,sK1))
    | ~ spl16_31 ),
    inference(avatar_component_clause,[],[f468])).

fof(f6281,plain,
    ( r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK1)
    | ~ spl16_314 ),
    inference(avatar_component_clause,[],[f6279])).

fof(f6282,plain,
    ( ~ spl16_37
    | spl16_314
    | ~ spl16_2
    | spl16_8 ),
    inference(avatar_split_clause,[],[f3463,f208,f175,f6279,f537])).

fof(f175,plain,
    ( spl16_2
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f3463,plain,
    ( r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK1)
    | ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0))
    | ~ spl16_2
    | spl16_8 ),
    inference(resolution,[],[f944,f210])).

fof(f210,plain,
    ( ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | spl16_8 ),
    inference(avatar_component_clause,[],[f208])).

fof(f944,plain,
    ( ! [X54,X52,X55,X53] :
        ( r2_hidden(k4_tarski(X52,X54),k6_subset_1(X55,k7_relat_1(sK2,X53)))
        | r2_hidden(X52,X53)
        | ~ r2_hidden(k4_tarski(X52,X54),X55) )
    | ~ spl16_2 ),
    inference(resolution,[],[f176,f119])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(sK2,X1))
        | r2_hidden(X0,X1) )
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f175])).

fof(f6272,plain,
    ( spl16_37
    | ~ spl16_4
    | ~ spl16_31
    | ~ spl16_32 ),
    inference(avatar_split_clause,[],[f6263,f473,f468,f183,f537])).

fof(f183,plain,
    ( spl16_4
  <=> ! [X7,X8,X6] :
        ( r2_hidden(k4_tarski(X6,X7),k7_relat_1(sK2,X8))
        | ~ r2_hidden(X6,X8)
        | ~ r2_hidden(k4_tarski(X6,X7),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f6263,plain,
    ( r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0))
    | ~ spl16_4
    | ~ spl16_31
    | ~ spl16_32 ),
    inference(resolution,[],[f2035,f1132])).

fof(f1132,plain,
    ( r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK0)
    | ~ spl16_31 ),
    inference(resolution,[],[f470,f121])).

fof(f121,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f102,f79])).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f2035,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),X0)
        | r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,X0)) )
    | ~ spl16_4
    | ~ spl16_32 ),
    inference(resolution,[],[f475,f184])).

fof(f184,plain,
    ( ! [X6,X8,X7] :
        ( ~ r2_hidden(k4_tarski(X6,X7),sK2)
        | ~ r2_hidden(X6,X8)
        | r2_hidden(k4_tarski(X6,X7),k7_relat_1(sK2,X8)) )
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f183])).

fof(f475,plain,
    ( r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK2)
    | ~ spl16_32 ),
    inference(avatar_component_clause,[],[f473])).

fof(f2190,plain,
    ( spl16_151
    | ~ spl16_107 ),
    inference(avatar_split_clause,[],[f1432,f1359,f2183])).

fof(f1432,plain,
    ( ! [X4] :
        ( sQ15_eqProxy(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)
        | ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)),X4)
        | ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
        | r2_hidden(sK11(X4),X4) )
    | ~ spl16_107 ),
    inference(resolution,[],[f1361,f131])).

fof(f131,plain,(
    ! [X0,X8,X1,X9] :
      ( sQ15_eqProxy(X0,X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | r2_hidden(sK11(X1),X1)
      | ~ sQ15_eqProxy(k4_tarski(X8,X9),sK12(X0)) ) ),
    inference(equality_proxy_replacement,[],[f92,f122,f122])).

fof(f92,plain,(
    ! [X0,X8,X1,X9] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | r2_hidden(sK11(X1),X1)
      | k4_tarski(X8,X9) != sK12(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2065,plain,(
    spl16_132 ),
    inference(avatar_contradiction_clause,[],[f2061])).

fof(f2061,plain,
    ( $false
    | spl16_132 ),
    inference(resolution,[],[f1746,f141])).

fof(f141,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f66,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1746,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl16_132 ),
    inference(avatar_component_clause,[],[f1744])).

fof(f2052,plain,(
    spl16_128 ),
    inference(avatar_contradiction_clause,[],[f2048])).

fof(f2048,plain,
    ( $false
    | spl16_128 ),
    inference(resolution,[],[f1700,f141])).

fof(f1700,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl16_128 ),
    inference(avatar_component_clause,[],[f1698])).

fof(f1362,plain,
    ( ~ spl16_30
    | spl16_107
    | ~ spl16_9 ),
    inference(avatar_split_clause,[],[f1356,f213,f1359,f464])).

fof(f1356,plain,
    ( sQ15_eqProxy(k4_tarski(sK6(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK7(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))
    | ~ v1_relat_1(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ spl16_9 ),
    inference(resolution,[],[f215,f128])).

fof(f128,plain,(
    ! [X4,X0] :
      ( sQ15_eqProxy(k4_tarski(sK6(X4),sK7(X4)),X4)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f75,f122])).

fof(f75,plain,(
    ! [X4,X0] :
      ( k4_tarski(sK6(X4),sK7(X4)) = X4
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK5(X0)
          & r2_hidden(sK5(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK6(X4),sK7(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f45,f47,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK5(X0)
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK6(X4),sK7(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f215,plain,
    ( r2_hidden(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ spl16_9 ),
    inference(avatar_component_clause,[],[f213])).

fof(f737,plain,
    ( ~ spl16_11
    | spl16_54
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f731,f218,f734,f247])).

fof(f247,plain,
    ( spl16_11
  <=> v1_relat_1(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).

fof(f731,plain,
    ( sQ15_eqProxy(k4_tarski(sK6(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK7(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))
    | ~ v1_relat_1(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | ~ spl16_10 ),
    inference(resolution,[],[f220,f128])).

fof(f220,plain,
    ( r2_hidden(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | ~ spl16_10 ),
    inference(avatar_component_clause,[],[f218])).

fof(f673,plain,(
    spl16_30 ),
    inference(avatar_contradiction_clause,[],[f669])).

fof(f669,plain,
    ( $false
    | spl16_30 ),
    inference(resolution,[],[f466,f141])).

fof(f466,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | spl16_30 ),
    inference(avatar_component_clause,[],[f464])).

fof(f599,plain,
    ( spl16_37
    | ~ spl16_8 ),
    inference(avatar_split_clause,[],[f584,f208,f537])).

fof(f584,plain,
    ( r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0))
    | ~ spl16_8 ),
    inference(resolution,[],[f209,f121])).

fof(f476,plain,
    ( ~ spl16_1
    | ~ spl16_30
    | spl16_32
    | ~ spl16_7 ),
    inference(avatar_split_clause,[],[f452,f204,f473,f464,f171])).

fof(f452,plain,
    ( r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl16_7 ),
    inference(resolution,[],[f205,f117])).

fof(f117,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f205,plain,
    ( r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ spl16_7 ),
    inference(avatar_component_clause,[],[f204])).

fof(f471,plain,
    ( ~ spl16_1
    | ~ spl16_30
    | spl16_31
    | ~ spl16_7 ),
    inference(avatar_split_clause,[],[f451,f204,f468,f464,f171])).

fof(f451,plain,
    ( r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl16_7 ),
    inference(resolution,[],[f205,f118])).

fof(f299,plain,(
    spl16_11 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl16_11 ),
    inference(resolution,[],[f265,f141])).

fof(f265,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl16_11 ),
    inference(resolution,[],[f249,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f83,f79])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f249,plain,
    ( ~ v1_relat_1(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | spl16_11 ),
    inference(avatar_component_clause,[],[f247])).

fof(f245,plain,(
    spl16_1 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl16_1 ),
    inference(resolution,[],[f173,f66])).

fof(f173,plain,
    ( ~ v1_relat_1(sK2)
    | spl16_1 ),
    inference(avatar_component_clause,[],[f171])).

fof(f226,plain,
    ( spl16_9
    | spl16_10
    | spl16_7
    | spl16_8 ),
    inference(avatar_split_clause,[],[f196,f208,f204,f218,f213])).

fof(f196,plain,
    ( r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | r2_hidden(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | r2_hidden(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f123,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( sQ15_eqProxy(X0,X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | r2_hidden(sK11(X1),X1)
      | r2_hidden(sK12(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f87,f122])).

fof(f87,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | r2_hidden(sK11(X1),X1)
      | r2_hidden(sK12(X0),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f225,plain,
    ( spl16_5
    | spl16_10
    | spl16_7
    | spl16_8 ),
    inference(avatar_split_clause,[],[f195,f208,f204,f218,f198])).

fof(f195,plain,(
    ! [X14,X15] :
      ( r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
      | r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
      | r2_hidden(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
      | ~ sQ15_eqProxy(k4_tarski(X14,X15),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))) ) ),
    inference(resolution,[],[f123,f135])).

fof(f135,plain,(
    ! [X0,X8,X1,X9] :
      ( sQ15_eqProxy(X0,X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | r2_hidden(sK11(X1),X1)
      | ~ sQ15_eqProxy(k4_tarski(X8,X9),sK12(X0)) ) ),
    inference(equality_proxy_replacement,[],[f88,f122,f122])).

fof(f88,plain,(
    ! [X0,X8,X1,X9] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | r2_hidden(sK11(X1),X1)
      | k4_tarski(X8,X9) != sK12(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f224,plain,
    ( spl16_9
    | spl16_6
    | spl16_7
    | spl16_8 ),
    inference(avatar_split_clause,[],[f194,f208,f204,f201,f213])).

fof(f194,plain,(
    ! [X12,X13] :
      ( r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
      | r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
      | ~ sQ15_eqProxy(k4_tarski(X12,X13),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))
      | r2_hidden(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) ) ),
    inference(resolution,[],[f123,f134])).

fof(f134,plain,(
    ! [X6,X0,X5,X1] :
      ( sQ15_eqProxy(X0,X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | ~ sQ15_eqProxy(k4_tarski(X5,X6),sK11(X1))
      | r2_hidden(sK12(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f89,f122,f122])).

fof(f89,plain,(
    ! [X6,X0,X5,X1] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK11(X1)
      | r2_hidden(sK12(X0),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f223,plain,
    ( spl16_5
    | spl16_6
    | spl16_7
    | spl16_8 ),
    inference(avatar_split_clause,[],[f193,f208,f204,f201,f198])).

fof(f193,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
      | r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
      | ~ sQ15_eqProxy(k4_tarski(X8,X9),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))
      | ~ sQ15_eqProxy(k4_tarski(X10,X11),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))) ) ),
    inference(resolution,[],[f123,f133])).

fof(f133,plain,(
    ! [X6,X0,X8,X5,X1,X9] :
      ( sQ15_eqProxy(X0,X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | ~ sQ15_eqProxy(k4_tarski(X5,X6),sK11(X1))
      | ~ sQ15_eqProxy(k4_tarski(X8,X9),sK12(X0)) ) ),
    inference(equality_proxy_replacement,[],[f90,f122,f122,f122])).

fof(f90,plain,(
    ! [X6,X0,X8,X5,X1,X9] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK11(X1)
      | k4_tarski(X8,X9) != sK12(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f222,plain,
    ( spl16_9
    | spl16_10
    | ~ spl16_7
    | ~ spl16_8 ),
    inference(avatar_split_clause,[],[f192,f208,f204,f218,f213])).

fof(f192,plain,
    ( ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | r2_hidden(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))
    | r2_hidden(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f123,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( sQ15_eqProxy(X0,X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | r2_hidden(sK11(X1),X1)
      | r2_hidden(sK12(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f91,f122])).

fof(f91,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | r2_hidden(sK11(X1),X1)
      | r2_hidden(sK12(X0),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f185,plain,
    ( ~ spl16_1
    | spl16_4 ),
    inference(avatar_split_clause,[],[f156,f183,f171])).

fof(f156,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(k4_tarski(X6,X7),k7_relat_1(sK2,X8))
      | ~ r2_hidden(k4_tarski(X6,X7),sK2)
      | ~ r2_hidden(X6,X8)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f141,f116])).

fof(f177,plain,
    ( ~ spl16_1
    | spl16_2 ),
    inference(avatar_split_clause,[],[f154,f175,f171])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f141,f118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:57:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (25424)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (25432)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (25439)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (25425)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (25430)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (25421)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (25423)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (25422)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (25419)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (25420)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (25433)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (25447)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (25446)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (25445)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (25442)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (25443)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (25444)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (25438)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (25421)Refutation not found, incomplete strategy% (25421)------------------------------
% 0.22/0.55  % (25421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (25421)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (25421)Memory used [KB]: 10746
% 0.22/0.55  % (25421)Time elapsed: 0.133 s
% 0.22/0.55  % (25421)------------------------------
% 0.22/0.55  % (25421)------------------------------
% 0.22/0.55  % (25434)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (25448)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (25440)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (25429)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (25441)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (25435)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (25436)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (25431)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (25427)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (25428)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (25437)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (25426)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (25441)Refutation not found, incomplete strategy% (25441)------------------------------
% 0.22/0.56  % (25441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (25441)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (25441)Memory used [KB]: 10746
% 0.22/0.56  % (25441)Time elapsed: 0.148 s
% 0.22/0.56  % (25441)------------------------------
% 0.22/0.56  % (25441)------------------------------
% 0.22/0.56  % (25436)Refutation not found, incomplete strategy% (25436)------------------------------
% 0.22/0.56  % (25436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (25436)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (25436)Memory used [KB]: 10618
% 0.22/0.56  % (25436)Time elapsed: 0.148 s
% 0.22/0.56  % (25436)------------------------------
% 0.22/0.56  % (25436)------------------------------
% 2.09/0.68  % (25460)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.09/0.70  % (25462)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.09/0.70  % (25461)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.10/0.82  % (25424)Time limit reached!
% 3.10/0.82  % (25424)------------------------------
% 3.10/0.82  % (25424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.84  % (25424)Termination reason: Time limit
% 3.10/0.84  % (25424)Termination phase: Saturation
% 3.10/0.84  
% 3.10/0.84  % (25424)Memory used [KB]: 10746
% 3.10/0.84  % (25424)Time elapsed: 0.400 s
% 3.10/0.84  % (25424)------------------------------
% 3.10/0.84  % (25424)------------------------------
% 3.93/0.92  % (25429)Time limit reached!
% 3.93/0.92  % (25429)------------------------------
% 3.93/0.92  % (25429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.92  % (25429)Termination reason: Time limit
% 3.93/0.92  
% 3.93/0.92  % (25429)Memory used [KB]: 11897
% 3.93/0.92  % (25429)Time elapsed: 0.508 s
% 3.93/0.92  % (25429)------------------------------
% 3.93/0.92  % (25429)------------------------------
% 4.25/0.93  % (25431)Time limit reached!
% 4.25/0.93  % (25431)------------------------------
% 4.25/0.93  % (25431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/0.93  % (25431)Termination reason: Time limit
% 4.25/0.93  % (25431)Termination phase: Saturation
% 4.25/0.93  
% 4.25/0.93  % (25431)Memory used [KB]: 8571
% 4.25/0.93  % (25431)Time elapsed: 0.500 s
% 4.25/0.93  % (25431)------------------------------
% 4.25/0.93  % (25431)------------------------------
% 4.25/0.93  % (25420)Time limit reached!
% 4.25/0.93  % (25420)------------------------------
% 4.25/0.93  % (25420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/0.93  % (25420)Termination reason: Time limit
% 4.25/0.93  
% 4.25/0.93  % (25420)Memory used [KB]: 8315
% 4.25/0.93  % (25420)Time elapsed: 0.517 s
% 4.25/0.93  % (25420)------------------------------
% 4.25/0.93  % (25420)------------------------------
% 4.25/0.93  % (25419)Time limit reached!
% 4.25/0.93  % (25419)------------------------------
% 4.25/0.93  % (25419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/0.93  % (25419)Termination reason: Time limit
% 4.25/0.93  
% 4.25/0.93  % (25419)Memory used [KB]: 4221
% 4.25/0.93  % (25419)Time elapsed: 0.517 s
% 4.25/0.93  % (25419)------------------------------
% 4.25/0.93  % (25419)------------------------------
% 4.25/0.93  % (25463)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.81/1.03  % (25435)Time limit reached!
% 4.81/1.03  % (25435)------------------------------
% 4.81/1.03  % (25435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.03  % (25435)Termination reason: Time limit
% 4.81/1.03  % (25435)Termination phase: Saturation
% 4.81/1.03  
% 4.81/1.03  % (25435)Memory used [KB]: 17014
% 4.81/1.03  % (25435)Time elapsed: 0.600 s
% 4.81/1.03  % (25435)------------------------------
% 4.81/1.03  % (25435)------------------------------
% 4.81/1.03  % (25447)Time limit reached!
% 4.81/1.03  % (25447)------------------------------
% 4.81/1.03  % (25447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.03  % (25447)Termination reason: Time limit
% 4.81/1.03  
% 4.81/1.03  % (25447)Memory used [KB]: 8443
% 4.81/1.03  % (25447)Time elapsed: 0.621 s
% 4.81/1.03  % (25447)------------------------------
% 4.81/1.03  % (25447)------------------------------
% 4.81/1.04  % (25464)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.81/1.05  % (25467)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.81/1.07  % (25466)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.64/1.08  % (25426)Time limit reached!
% 5.64/1.08  % (25426)------------------------------
% 5.64/1.08  % (25426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.64/1.08  % (25426)Termination reason: Time limit
% 5.64/1.08  % (25426)Termination phase: Saturation
% 5.64/1.08  
% 5.64/1.08  % (25426)Memory used [KB]: 10618
% 5.64/1.08  % (25426)Time elapsed: 0.600 s
% 5.64/1.08  % (25426)------------------------------
% 5.64/1.08  % (25426)------------------------------
% 5.64/1.08  % (25465)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.64/1.15  % (25469)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.33/1.17  % (25468)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.57/1.22  % (25471)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.82/1.23  % (25440)Time limit reached!
% 6.82/1.23  % (25440)------------------------------
% 6.82/1.23  % (25440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.82/1.23  % (25440)Termination reason: Time limit
% 6.82/1.23  
% 6.82/1.23  % (25440)Memory used [KB]: 6268
% 6.82/1.23  % (25440)Time elapsed: 0.820 s
% 6.82/1.23  % (25440)------------------------------
% 6.82/1.23  % (25440)------------------------------
% 7.34/1.31  % (25463)Time limit reached!
% 7.34/1.31  % (25463)------------------------------
% 7.34/1.31  % (25463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.34/1.31  % (25463)Termination reason: Time limit
% 7.34/1.31  % (25463)Termination phase: Saturation
% 7.34/1.31  
% 7.34/1.31  % (25463)Memory used [KB]: 9722
% 7.34/1.31  % (25463)Time elapsed: 0.400 s
% 7.34/1.31  % (25463)------------------------------
% 7.34/1.31  % (25463)------------------------------
% 7.34/1.36  % (25537)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.34/1.36  % (25464)Time limit reached!
% 7.34/1.36  % (25464)------------------------------
% 7.34/1.36  % (25464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.34/1.36  % (25464)Termination reason: Time limit
% 7.34/1.36  
% 7.34/1.36  % (25464)Memory used [KB]: 13176
% 7.34/1.36  % (25464)Time elapsed: 0.409 s
% 7.34/1.36  % (25464)------------------------------
% 7.34/1.36  % (25464)------------------------------
% 7.88/1.43  % (25593)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 8.70/1.50  % (25618)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.85/1.61  % (25445)Time limit reached!
% 9.85/1.61  % (25445)------------------------------
% 9.85/1.61  % (25445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.85/1.61  % (25445)Termination reason: Time limit
% 9.85/1.61  % (25445)Termination phase: Saturation
% 9.85/1.61  
% 9.85/1.61  % (25445)Memory used [KB]: 17782
% 9.85/1.61  % (25445)Time elapsed: 1.200 s
% 9.85/1.61  % (25445)------------------------------
% 9.85/1.61  % (25445)------------------------------
% 10.38/1.73  % (25434)Refutation found. Thanks to Tanya!
% 10.38/1.73  % SZS status Theorem for theBenchmark
% 10.38/1.74  % (25686)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 10.38/1.75  % SZS output start Proof for theBenchmark
% 10.38/1.75  fof(f9681,plain,(
% 10.38/1.75    $false),
% 10.38/1.75    inference(avatar_sat_refutation,[],[f177,f185,f222,f223,f224,f225,f226,f245,f299,f471,f476,f599,f673,f737,f1362,f2052,f2065,f2190,f6272,f6282,f9355,f9358,f9359,f9361,f9417,f9419,f9435,f9474,f9650,f9660,f9661,f9673])).
% 10.38/1.75  fof(f9673,plain,(
% 10.38/1.75    ~spl16_38 | ~spl16_8),
% 10.38/1.75    inference(avatar_split_clause,[],[f1182,f208,f541])).
% 10.38/1.75  fof(f541,plain,(
% 10.38/1.75    spl16_38 <=> r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_38])])).
% 10.38/1.75  fof(f208,plain,(
% 10.38/1.75    spl16_8 <=> r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).
% 10.38/1.75  fof(f1182,plain,(
% 10.38/1.75    ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1)) | ~spl16_8),
% 10.38/1.75    inference(resolution,[],[f209,f120])).
% 10.38/1.75  fof(f120,plain,(
% 10.38/1.75    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 10.38/1.75    inference(equality_resolution,[],[f114])).
% 10.38/1.75  fof(f114,plain,(
% 10.38/1.75    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 10.38/1.75    inference(definition_unfolding,[],[f103,f79])).
% 10.38/1.75  fof(f79,plain,(
% 10.38/1.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 10.38/1.75    inference(cnf_transformation,[],[f7])).
% 10.38/1.75  fof(f7,axiom,(
% 10.38/1.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 10.38/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 10.38/1.75  fof(f103,plain,(
% 10.38/1.75    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 10.38/1.75    inference(cnf_transformation,[],[f65])).
% 10.38/1.75  fof(f65,plain,(
% 10.38/1.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK14(X0,X1,X2),X1) | ~r2_hidden(sK14(X0,X1,X2),X0) | ~r2_hidden(sK14(X0,X1,X2),X2)) & ((~r2_hidden(sK14(X0,X1,X2),X1) & r2_hidden(sK14(X0,X1,X2),X0)) | r2_hidden(sK14(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 10.38/1.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f63,f64])).
% 10.38/1.75  fof(f64,plain,(
% 10.38/1.75    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK14(X0,X1,X2),X1) | ~r2_hidden(sK14(X0,X1,X2),X0) | ~r2_hidden(sK14(X0,X1,X2),X2)) & ((~r2_hidden(sK14(X0,X1,X2),X1) & r2_hidden(sK14(X0,X1,X2),X0)) | r2_hidden(sK14(X0,X1,X2),X2))))),
% 10.38/1.75    introduced(choice_axiom,[])).
% 10.38/1.75  fof(f63,plain,(
% 10.38/1.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 10.38/1.75    inference(rectify,[],[f62])).
% 10.38/1.75  fof(f62,plain,(
% 10.38/1.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 10.38/1.75    inference(flattening,[],[f61])).
% 10.38/1.75  fof(f61,plain,(
% 10.38/1.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 10.38/1.75    inference(nnf_transformation,[],[f2])).
% 10.38/1.75  fof(f2,axiom,(
% 10.38/1.75    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 10.38/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 10.38/1.75  fof(f209,plain,(
% 10.38/1.75    r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~spl16_8),
% 10.38/1.75    inference(avatar_component_clause,[],[f208])).
% 10.38/1.75  fof(f9661,plain,(
% 10.38/1.75    spl16_32 | ~spl16_37),
% 10.38/1.75    inference(avatar_split_clause,[],[f6369,f537,f473])).
% 10.38/1.75  fof(f473,plain,(
% 10.38/1.75    spl16_32 <=> r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK2)),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_32])])).
% 10.38/1.75  fof(f537,plain,(
% 10.38/1.75    spl16_37 <=> r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_37])])).
% 10.38/1.75  fof(f6369,plain,(
% 10.38/1.75    r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK2) | ~spl16_37),
% 10.38/1.75    inference(resolution,[],[f1822,f142])).
% 10.38/1.75  fof(f142,plain,(
% 10.38/1.75    ( ! [X1] : (r1_tarski(k7_relat_1(sK2,X1),sK2)) )),
% 10.38/1.75    inference(resolution,[],[f66,f85])).
% 10.38/1.75  fof(f85,plain,(
% 10.38/1.75    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 10.38/1.75    inference(cnf_transformation,[],[f28])).
% 10.38/1.75  fof(f28,plain,(
% 10.38/1.75    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 10.38/1.75    inference(ennf_transformation,[],[f16])).
% 10.38/1.75  fof(f16,axiom,(
% 10.38/1.75    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 10.38/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 10.38/1.75  fof(f66,plain,(
% 10.38/1.75    v1_relat_1(sK2)),
% 10.38/1.75    inference(cnf_transformation,[],[f38])).
% 10.38/1.75  fof(f38,plain,(
% 10.38/1.75    k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 10.38/1.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f37])).
% 10.38/1.75  fof(f37,plain,(
% 10.38/1.75    ? [X0,X1,X2] : (k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) & v1_relat_1(X2)) => (k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 10.38/1.75    introduced(choice_axiom,[])).
% 10.38/1.75  fof(f21,plain,(
% 10.38/1.75    ? [X0,X1,X2] : (k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) & v1_relat_1(X2))),
% 10.38/1.75    inference(ennf_transformation,[],[f18])).
% 10.38/1.75  fof(f18,negated_conjecture,(
% 10.38/1.75    ~! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 10.38/1.75    inference(negated_conjecture,[],[f17])).
% 10.38/1.75  fof(f17,conjecture,(
% 10.38/1.75    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 10.38/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).
% 10.38/1.75  fof(f1822,plain,(
% 10.38/1.75    ( ! [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),X3) | r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),X3)) ) | ~spl16_37),
% 10.38/1.75    inference(resolution,[],[f538,f95])).
% 10.38/1.75  fof(f95,plain,(
% 10.38/1.75    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 10.38/1.75    inference(cnf_transformation,[],[f59])).
% 10.38/1.75  fof(f59,plain,(
% 10.38/1.75    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK13(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 10.38/1.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f57,f58])).
% 10.38/1.75  fof(f58,plain,(
% 10.38/1.75    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK13(X0,X1),X0)))),
% 10.38/1.75    introduced(choice_axiom,[])).
% 10.38/1.75  fof(f57,plain,(
% 10.38/1.75    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 10.38/1.75    inference(rectify,[],[f56])).
% 10.38/1.75  fof(f56,plain,(
% 10.38/1.75    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 10.38/1.75    inference(nnf_transformation,[],[f33])).
% 10.38/1.75  fof(f33,plain,(
% 10.38/1.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 10.38/1.75    inference(ennf_transformation,[],[f1])).
% 10.38/1.75  fof(f1,axiom,(
% 10.38/1.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 10.38/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 10.38/1.75  fof(f538,plain,(
% 10.38/1.75    r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0)) | ~spl16_37),
% 10.38/1.75    inference(avatar_component_clause,[],[f537])).
% 10.38/1.75  fof(f9660,plain,(
% 10.38/1.75    ~spl16_1 | ~spl16_30 | ~spl16_31 | ~spl16_32 | spl16_7),
% 10.38/1.75    inference(avatar_split_clause,[],[f1169,f204,f473,f468,f464,f171])).
% 10.38/1.75  fof(f171,plain,(
% 10.38/1.75    spl16_1 <=> v1_relat_1(sK2)),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).
% 10.38/1.75  fof(f464,plain,(
% 10.38/1.75    spl16_30 <=> v1_relat_1(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_30])])).
% 10.38/1.75  fof(f468,plain,(
% 10.38/1.75    spl16_31 <=> r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(sK0,sK1))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_31])])).
% 10.38/1.75  fof(f204,plain,(
% 10.38/1.75    spl16_7 <=> r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_7])])).
% 10.38/1.75  fof(f1169,plain,(
% 10.38/1.75    ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK2) | ~r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(sK0,sK1)) | ~v1_relat_1(k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~v1_relat_1(sK2) | spl16_7),
% 10.38/1.75    inference(resolution,[],[f206,f116])).
% 10.38/1.75  fof(f116,plain,(
% 10.38/1.75    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 10.38/1.75    inference(equality_resolution,[],[f71])).
% 10.38/1.75  fof(f71,plain,(
% 10.38/1.75    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 10.38/1.75    inference(cnf_transformation,[],[f43])).
% 10.38/1.75  fof(f43,plain,(
% 10.38/1.75    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 10.38/1.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f41,f42])).
% 10.38/1.75  fof(f42,plain,(
% 10.38/1.75    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 10.38/1.75    introduced(choice_axiom,[])).
% 10.38/1.75  fof(f41,plain,(
% 10.38/1.75    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 10.38/1.75    inference(rectify,[],[f40])).
% 10.38/1.75  fof(f40,plain,(
% 10.38/1.75    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 10.38/1.75    inference(flattening,[],[f39])).
% 10.38/1.75  fof(f39,plain,(
% 10.38/1.75    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 10.38/1.75    inference(nnf_transformation,[],[f23])).
% 10.38/1.75  fof(f23,plain,(
% 10.38/1.75    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 10.38/1.75    inference(ennf_transformation,[],[f12])).
% 10.38/1.75  fof(f12,axiom,(
% 10.38/1.75    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 10.38/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
% 10.38/1.75  fof(f206,plain,(
% 10.38/1.75    ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | spl16_7),
% 10.38/1.75    inference(avatar_component_clause,[],[f204])).
% 10.38/1.75  fof(f9650,plain,(
% 10.38/1.75    ~spl16_394 | spl16_314 | spl16_31),
% 10.38/1.75    inference(avatar_split_clause,[],[f9644,f468,f6279,f9421])).
% 10.38/1.75  fof(f9421,plain,(
% 10.38/1.75    spl16_394 <=> r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK0)),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_394])])).
% 10.38/1.75  fof(f6279,plain,(
% 10.38/1.75    spl16_314 <=> r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK1)),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_314])])).
% 10.38/1.75  fof(f9644,plain,(
% 10.38/1.75    r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK1) | ~r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK0) | spl16_31),
% 10.38/1.75    inference(resolution,[],[f469,f119])).
% 10.38/1.75  fof(f119,plain,(
% 10.38/1.75    ( ! [X4,X0,X1] : (r2_hidden(X4,k6_subset_1(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 10.38/1.75    inference(equality_resolution,[],[f113])).
% 10.38/1.75  fof(f113,plain,(
% 10.38/1.75    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k6_subset_1(X0,X1) != X2) )),
% 10.38/1.75    inference(definition_unfolding,[],[f104,f79])).
% 10.38/1.75  fof(f104,plain,(
% 10.38/1.75    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 10.38/1.75    inference(cnf_transformation,[],[f65])).
% 10.38/1.75  fof(f469,plain,(
% 10.38/1.75    ~r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(sK0,sK1)) | spl16_31),
% 10.38/1.75    inference(avatar_component_clause,[],[f468])).
% 10.38/1.75  fof(f9474,plain,(
% 10.38/1.75    ~spl16_6 | ~spl16_54),
% 10.38/1.75    inference(avatar_contradiction_clause,[],[f9453])).
% 10.38/1.75  fof(f9453,plain,(
% 10.38/1.75    $false | (~spl16_6 | ~spl16_54)),
% 10.38/1.75    inference(resolution,[],[f202,f736])).
% 10.38/1.75  fof(f736,plain,(
% 10.38/1.75    sQ15_eqProxy(k4_tarski(sK6(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK7(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))) | ~spl16_54),
% 10.38/1.75    inference(avatar_component_clause,[],[f734])).
% 10.38/1.75  fof(f734,plain,(
% 10.38/1.75    spl16_54 <=> sQ15_eqProxy(k4_tarski(sK6(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK7(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_54])])).
% 10.38/1.75  fof(f202,plain,(
% 10.38/1.75    ( ! [X0,X1] : (~sQ15_eqProxy(k4_tarski(X0,X1),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))) ) | ~spl16_6),
% 10.38/1.75    inference(avatar_component_clause,[],[f201])).
% 10.38/1.75  fof(f201,plain,(
% 10.38/1.75    spl16_6 <=> ! [X1,X0] : ~sQ15_eqProxy(k4_tarski(X0,X1),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).
% 10.38/1.75  fof(f9435,plain,(
% 10.38/1.75    ~spl16_1 | ~spl16_128 | spl16_394 | ~spl16_37),
% 10.38/1.75    inference(avatar_split_clause,[],[f1817,f537,f9421,f1698,f171])).
% 10.38/1.75  fof(f1698,plain,(
% 10.38/1.75    spl16_128 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_128])])).
% 10.38/1.75  fof(f1817,plain,(
% 10.38/1.75    r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK0) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl16_37),
% 10.38/1.75    inference(resolution,[],[f538,f118])).
% 10.38/1.75  fof(f118,plain,(
% 10.38/1.75    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 10.38/1.75    inference(equality_resolution,[],[f69])).
% 10.38/1.75  fof(f69,plain,(
% 10.38/1.75    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 10.38/1.75    inference(cnf_transformation,[],[f43])).
% 10.38/1.75  fof(f9419,plain,(
% 10.38/1.75    ~spl16_1 | ~spl16_132 | ~spl16_314 | ~spl16_32 | spl16_38),
% 10.38/1.75    inference(avatar_split_clause,[],[f2192,f541,f473,f6279,f1744,f171])).
% 10.38/1.75  fof(f1744,plain,(
% 10.38/1.75    spl16_132 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_132])])).
% 10.38/1.75  fof(f2192,plain,(
% 10.38/1.75    ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK2) | ~r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | spl16_38),
% 10.38/1.75    inference(resolution,[],[f542,f116])).
% 10.38/1.75  fof(f542,plain,(
% 10.38/1.75    ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK1)) | spl16_38),
% 10.38/1.75    inference(avatar_component_clause,[],[f541])).
% 10.38/1.75  fof(f9417,plain,(
% 10.38/1.75    ~spl16_5 | ~spl16_107),
% 10.38/1.75    inference(avatar_contradiction_clause,[],[f9400])).
% 10.38/1.75  fof(f9400,plain,(
% 10.38/1.75    $false | (~spl16_5 | ~spl16_107)),
% 10.38/1.75    inference(resolution,[],[f199,f1361])).
% 10.38/1.75  fof(f1361,plain,(
% 10.38/1.75    sQ15_eqProxy(k4_tarski(sK6(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK7(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))) | ~spl16_107),
% 10.38/1.75    inference(avatar_component_clause,[],[f1359])).
% 10.38/1.75  fof(f1359,plain,(
% 10.38/1.75    spl16_107 <=> sQ15_eqProxy(k4_tarski(sK6(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK7(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_107])])).
% 10.38/1.75  fof(f199,plain,(
% 10.38/1.75    ( ! [X2,X3] : (~sQ15_eqProxy(k4_tarski(X2,X3),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))) ) | ~spl16_5),
% 10.38/1.75    inference(avatar_component_clause,[],[f198])).
% 10.38/1.75  fof(f198,plain,(
% 10.38/1.75    spl16_5 <=> ! [X3,X2] : ~sQ15_eqProxy(k4_tarski(X2,X3),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).
% 10.38/1.75  fof(f9361,plain,(
% 10.38/1.75    ~spl16_8 | ~spl16_7 | spl16_10 | ~spl16_151),
% 10.38/1.75    inference(avatar_split_clause,[],[f6563,f2183,f218,f204,f208])).
% 10.38/1.75  fof(f218,plain,(
% 10.38/1.75    spl16_10 <=> r2_hidden(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).
% 10.38/1.75  fof(f2183,plain,(
% 10.38/1.75    spl16_151 <=> ! [X4] : (sQ15_eqProxy(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4) | r2_hidden(sK11(X4),X4) | ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)),X4))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_151])])).
% 10.38/1.75  fof(f6563,plain,(
% 10.38/1.75    r2_hidden(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~spl16_151),
% 10.38/1.75    inference(resolution,[],[f2184,f123])).
% 10.38/1.75  fof(f123,plain,(
% 10.38/1.75    ~sQ15_eqProxy(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),
% 10.38/1.75    inference(equality_proxy_replacement,[],[f67,f122])).
% 10.38/1.75  fof(f122,plain,(
% 10.38/1.75    ! [X1,X0] : (sQ15_eqProxy(X0,X1) <=> X0 = X1)),
% 10.38/1.75    introduced(equality_proxy_definition,[new_symbols(naming,[sQ15_eqProxy])])).
% 10.38/1.75  fof(f67,plain,(
% 10.38/1.75    k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),
% 10.38/1.75    inference(cnf_transformation,[],[f38])).
% 10.38/1.75  fof(f2184,plain,(
% 10.38/1.75    ( ! [X4] : (sQ15_eqProxy(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4) | r2_hidden(sK11(X4),X4) | ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)),X4)) ) | ~spl16_151),
% 10.38/1.75    inference(avatar_component_clause,[],[f2183])).
% 10.38/1.75  fof(f9359,plain,(
% 10.38/1.75    spl16_9 | ~spl16_7 | ~spl16_8 | ~spl16_54),
% 10.38/1.75    inference(avatar_split_clause,[],[f6844,f734,f208,f204,f213])).
% 10.38/1.75  fof(f213,plain,(
% 10.38/1.75    spl16_9 <=> r2_hidden(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 10.38/1.75    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).
% 10.38/1.75  fof(f6844,plain,(
% 10.38/1.75    ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | r2_hidden(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~spl16_54),
% 10.38/1.75    inference(resolution,[],[f1482,f123])).
% 10.38/1.75  fof(f1482,plain,(
% 10.38/1.75    ( ! [X4] : (sQ15_eqProxy(X4,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~r2_hidden(k4_tarski(sK9(X4,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(X4,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~r2_hidden(k4_tarski(sK9(X4,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(X4,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),X4) | r2_hidden(sK12(X4),X4)) ) | ~spl16_54),
% 10.38/1.75    inference(resolution,[],[f736,f130])).
% 10.38/1.75  fof(f130,plain,(
% 10.38/1.75    ( ! [X6,X0,X5,X1] : (sQ15_eqProxy(X0,X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | ~sQ15_eqProxy(k4_tarski(X5,X6),sK11(X1)) | r2_hidden(sK12(X0),X0)) )),
% 10.38/1.75    inference(equality_proxy_replacement,[],[f93,f122,f122])).
% 10.38/1.75  fof(f93,plain,(
% 10.38/1.75    ( ! [X6,X0,X5,X1] : (X0 = X1 | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | k4_tarski(X5,X6) != sK11(X1) | r2_hidden(sK12(X0),X0)) )),
% 10.38/1.75    inference(cnf_transformation,[],[f55])).
% 10.38/1.75  fof(f55,plain,(
% 10.38/1.75    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0))) | (! [X5,X6] : k4_tarski(X5,X6) != sK11(X1) & r2_hidden(sK11(X1),X1)) | (! [X8,X9] : k4_tarski(X8,X9) != sK12(X0) & r2_hidden(sK12(X0),X0)))),
% 10.38/1.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f51,f54,f53,f52])).
% 10.38/1.75  fof(f52,plain,(
% 10.38/1.75    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0))) => ((~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0))))),
% 10.38/1.75    introduced(choice_axiom,[])).
% 10.38/1.75  fof(f53,plain,(
% 10.38/1.75    ! [X1] : (? [X4] : (! [X5,X6] : k4_tarski(X5,X6) != X4 & r2_hidden(X4,X1)) => (! [X6,X5] : k4_tarski(X5,X6) != sK11(X1) & r2_hidden(sK11(X1),X1)))),
% 10.38/1.75    introduced(choice_axiom,[])).
% 10.38/1.75  fof(f54,plain,(
% 10.38/1.75    ! [X0] : (? [X7] : (! [X8,X9] : k4_tarski(X8,X9) != X7 & r2_hidden(X7,X0)) => (! [X9,X8] : k4_tarski(X8,X9) != sK12(X0) & r2_hidden(sK12(X0),X0)))),
% 10.38/1.75    introduced(choice_axiom,[])).
% 10.38/1.75  fof(f51,plain,(
% 10.38/1.75    ! [X0,X1] : (X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0))) | ? [X4] : (! [X5,X6] : k4_tarski(X5,X6) != X4 & r2_hidden(X4,X1)) | ? [X7] : (! [X8,X9] : k4_tarski(X8,X9) != X7 & r2_hidden(X7,X0)))),
% 10.38/1.75    inference(nnf_transformation,[],[f32])).
% 10.38/1.75  fof(f32,plain,(
% 10.38/1.75    ! [X0,X1] : (X0 = X1 | ? [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <~> r2_hidden(k4_tarski(X2,X3),X1)) | ? [X4] : (! [X5,X6] : k4_tarski(X5,X6) != X4 & r2_hidden(X4,X1)) | ? [X7] : (! [X8,X9] : k4_tarski(X8,X9) != X7 & r2_hidden(X7,X0)))),
% 10.38/1.75    inference(flattening,[],[f31])).
% 10.38/1.75  fof(f31,plain,(
% 10.38/1.75    ! [X0,X1] : (X0 = X1 | (? [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <~> r2_hidden(k4_tarski(X2,X3),X1)) | ? [X4] : (! [X5,X6] : k4_tarski(X5,X6) != X4 & r2_hidden(X4,X1)) | ? [X7] : (! [X8,X9] : k4_tarski(X8,X9) != X7 & r2_hidden(X7,X0))))),
% 10.38/1.75    inference(ennf_transformation,[],[f20])).
% 10.38/1.75  fof(f20,plain,(
% 10.38/1.75    ! [X0,X1] : ((! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)) & ! [X4] : ~(! [X5,X6] : k4_tarski(X5,X6) != X4 & r2_hidden(X4,X1)) & ! [X7] : ~(! [X8,X9] : k4_tarski(X8,X9) != X7 & r2_hidden(X7,X0))) => X0 = X1)),
% 10.38/1.75    inference(rectify,[],[f6])).
% 10.38/1.75  fof(f6,axiom,(
% 10.38/1.75    ! [X0,X1] : ((! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)) & ! [X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X2 & r2_hidden(X2,X1)) & ! [X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X2 & r2_hidden(X2,X0))) => X0 = X1)),
% 10.38/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l131_zfmisc_1)).
% 10.38/1.75  fof(f9358,plain,(
% 10.38/1.75    spl16_5 | ~spl16_7 | ~spl16_8 | ~spl16_54),
% 10.38/1.75    inference(avatar_split_clause,[],[f6965,f734,f208,f204,f198])).
% 10.38/1.75  fof(f6965,plain,(
% 10.38/1.75    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~sQ15_eqProxy(k4_tarski(X0,X1),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))) ) | ~spl16_54),
% 10.38/1.75    inference(resolution,[],[f1483,f123])).
% 10.38/1.75  fof(f1483,plain,(
% 10.38/1.75    ( ! [X6,X7,X5] : (sQ15_eqProxy(X5,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~r2_hidden(k4_tarski(sK9(X5,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(X5,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~r2_hidden(k4_tarski(sK9(X5,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(X5,k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),X5) | ~sQ15_eqProxy(k4_tarski(X6,X7),sK12(X5))) ) | ~spl16_54),
% 10.38/1.75    inference(resolution,[],[f736,f129])).
% 10.38/1.75  fof(f129,plain,(
% 10.38/1.75    ( ! [X6,X0,X8,X5,X1,X9] : (sQ15_eqProxy(X0,X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | ~sQ15_eqProxy(k4_tarski(X5,X6),sK11(X1)) | ~sQ15_eqProxy(k4_tarski(X8,X9),sK12(X0))) )),
% 10.38/1.75    inference(equality_proxy_replacement,[],[f94,f122,f122,f122])).
% 10.38/1.75  fof(f94,plain,(
% 10.38/1.75    ( ! [X6,X0,X8,X5,X1,X9] : (X0 = X1 | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | k4_tarski(X5,X6) != sK11(X1) | k4_tarski(X8,X9) != sK12(X0)) )),
% 10.38/1.75    inference(cnf_transformation,[],[f55])).
% 10.38/1.75  fof(f9355,plain,(
% 10.38/1.75    ~spl16_31 | ~spl16_314),
% 10.38/1.75    inference(avatar_contradiction_clause,[],[f9343])).
% 10.38/1.75  fof(f9343,plain,(
% 10.38/1.75    $false | (~spl16_31 | ~spl16_314)),
% 10.38/1.75    inference(resolution,[],[f6281,f1133])).
% 10.38/1.75  fof(f1133,plain,(
% 10.38/1.75    ~r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK1) | ~spl16_31),
% 10.38/1.75    inference(resolution,[],[f470,f120])).
% 10.38/1.76  fof(f470,plain,(
% 10.38/1.76    r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(sK0,sK1)) | ~spl16_31),
% 10.38/1.76    inference(avatar_component_clause,[],[f468])).
% 10.38/1.76  fof(f6281,plain,(
% 10.38/1.76    r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK1) | ~spl16_314),
% 10.38/1.76    inference(avatar_component_clause,[],[f6279])).
% 10.38/1.76  fof(f6282,plain,(
% 10.38/1.76    ~spl16_37 | spl16_314 | ~spl16_2 | spl16_8),
% 10.38/1.76    inference(avatar_split_clause,[],[f3463,f208,f175,f6279,f537])).
% 10.38/1.76  fof(f175,plain,(
% 10.38/1.76    spl16_2 <=> ! [X1,X0,X2] : (r2_hidden(X0,X1) | ~r2_hidden(k4_tarski(X0,X2),k7_relat_1(sK2,X1)))),
% 10.38/1.76    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).
% 10.38/1.76  fof(f3463,plain,(
% 10.38/1.76    r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK1) | ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0)) | (~spl16_2 | spl16_8)),
% 10.38/1.76    inference(resolution,[],[f944,f210])).
% 10.38/1.76  fof(f210,plain,(
% 10.38/1.76    ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | spl16_8),
% 10.38/1.76    inference(avatar_component_clause,[],[f208])).
% 10.38/1.76  fof(f944,plain,(
% 10.38/1.76    ( ! [X54,X52,X55,X53] : (r2_hidden(k4_tarski(X52,X54),k6_subset_1(X55,k7_relat_1(sK2,X53))) | r2_hidden(X52,X53) | ~r2_hidden(k4_tarski(X52,X54),X55)) ) | ~spl16_2),
% 10.38/1.76    inference(resolution,[],[f176,f119])).
% 10.38/1.76  fof(f176,plain,(
% 10.38/1.76    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X2),k7_relat_1(sK2,X1)) | r2_hidden(X0,X1)) ) | ~spl16_2),
% 10.38/1.76    inference(avatar_component_clause,[],[f175])).
% 10.38/1.76  fof(f6272,plain,(
% 10.38/1.76    spl16_37 | ~spl16_4 | ~spl16_31 | ~spl16_32),
% 10.38/1.76    inference(avatar_split_clause,[],[f6263,f473,f468,f183,f537])).
% 10.38/1.76  fof(f183,plain,(
% 10.38/1.76    spl16_4 <=> ! [X7,X8,X6] : (r2_hidden(k4_tarski(X6,X7),k7_relat_1(sK2,X8)) | ~r2_hidden(X6,X8) | ~r2_hidden(k4_tarski(X6,X7),sK2))),
% 10.38/1.76    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).
% 10.38/1.76  fof(f6263,plain,(
% 10.38/1.76    r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0)) | (~spl16_4 | ~spl16_31 | ~spl16_32)),
% 10.38/1.76    inference(resolution,[],[f2035,f1132])).
% 10.38/1.76  fof(f1132,plain,(
% 10.38/1.76    r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK0) | ~spl16_31),
% 10.38/1.76    inference(resolution,[],[f470,f121])).
% 10.38/1.76  fof(f121,plain,(
% 10.38/1.76    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 10.38/1.76    inference(equality_resolution,[],[f115])).
% 10.38/1.76  fof(f115,plain,(
% 10.38/1.76    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 10.38/1.76    inference(definition_unfolding,[],[f102,f79])).
% 10.38/1.76  fof(f102,plain,(
% 10.38/1.76    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 10.38/1.76    inference(cnf_transformation,[],[f65])).
% 10.38/1.76  fof(f2035,plain,(
% 10.38/1.76    ( ! [X0] : (~r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),X0) | r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,X0))) ) | (~spl16_4 | ~spl16_32)),
% 10.38/1.76    inference(resolution,[],[f475,f184])).
% 10.38/1.76  fof(f184,plain,(
% 10.38/1.76    ( ! [X6,X8,X7] : (~r2_hidden(k4_tarski(X6,X7),sK2) | ~r2_hidden(X6,X8) | r2_hidden(k4_tarski(X6,X7),k7_relat_1(sK2,X8))) ) | ~spl16_4),
% 10.38/1.76    inference(avatar_component_clause,[],[f183])).
% 10.38/1.76  fof(f475,plain,(
% 10.38/1.76    r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK2) | ~spl16_32),
% 10.38/1.76    inference(avatar_component_clause,[],[f473])).
% 10.38/1.76  fof(f2190,plain,(
% 10.38/1.76    spl16_151 | ~spl16_107),
% 10.38/1.76    inference(avatar_split_clause,[],[f1432,f1359,f2183])).
% 10.38/1.76  fof(f1432,plain,(
% 10.38/1.76    ( ! [X4] : (sQ15_eqProxy(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4) | ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)),X4) | ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | r2_hidden(sK11(X4),X4)) ) | ~spl16_107),
% 10.38/1.76    inference(resolution,[],[f1361,f131])).
% 10.38/1.76  fof(f131,plain,(
% 10.38/1.76    ( ! [X0,X8,X1,X9] : (sQ15_eqProxy(X0,X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | r2_hidden(sK11(X1),X1) | ~sQ15_eqProxy(k4_tarski(X8,X9),sK12(X0))) )),
% 10.38/1.76    inference(equality_proxy_replacement,[],[f92,f122,f122])).
% 10.38/1.76  fof(f92,plain,(
% 10.38/1.76    ( ! [X0,X8,X1,X9] : (X0 = X1 | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | r2_hidden(sK11(X1),X1) | k4_tarski(X8,X9) != sK12(X0)) )),
% 10.38/1.76    inference(cnf_transformation,[],[f55])).
% 10.38/1.76  fof(f2065,plain,(
% 10.38/1.76    spl16_132),
% 10.38/1.76    inference(avatar_contradiction_clause,[],[f2061])).
% 10.38/1.76  fof(f2061,plain,(
% 10.38/1.76    $false | spl16_132),
% 10.38/1.76    inference(resolution,[],[f1746,f141])).
% 10.38/1.76  fof(f141,plain,(
% 10.38/1.76    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 10.38/1.76    inference(resolution,[],[f66,f84])).
% 10.38/1.76  fof(f84,plain,(
% 10.38/1.76    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 10.38/1.76    inference(cnf_transformation,[],[f27])).
% 10.38/1.76  fof(f27,plain,(
% 10.38/1.76    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 10.38/1.76    inference(ennf_transformation,[],[f14])).
% 10.38/1.76  fof(f14,axiom,(
% 10.38/1.76    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 10.38/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 10.38/1.76  fof(f1746,plain,(
% 10.38/1.76    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl16_132),
% 10.38/1.76    inference(avatar_component_clause,[],[f1744])).
% 10.38/1.76  fof(f2052,plain,(
% 10.38/1.76    spl16_128),
% 10.38/1.76    inference(avatar_contradiction_clause,[],[f2048])).
% 10.38/1.76  fof(f2048,plain,(
% 10.38/1.76    $false | spl16_128),
% 10.38/1.76    inference(resolution,[],[f1700,f141])).
% 10.38/1.76  fof(f1700,plain,(
% 10.38/1.76    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl16_128),
% 10.38/1.76    inference(avatar_component_clause,[],[f1698])).
% 10.38/1.76  fof(f1362,plain,(
% 10.38/1.76    ~spl16_30 | spl16_107 | ~spl16_9),
% 10.38/1.76    inference(avatar_split_clause,[],[f1356,f213,f1359,f464])).
% 10.38/1.76  fof(f1356,plain,(
% 10.38/1.76    sQ15_eqProxy(k4_tarski(sK6(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK7(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1)))) | ~v1_relat_1(k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~spl16_9),
% 10.38/1.76    inference(resolution,[],[f215,f128])).
% 10.38/1.76  fof(f128,plain,(
% 10.38/1.76    ( ! [X4,X0] : (sQ15_eqProxy(k4_tarski(sK6(X4),sK7(X4)),X4) | ~r2_hidden(X4,X0) | ~v1_relat_1(X0)) )),
% 10.38/1.76    inference(equality_proxy_replacement,[],[f75,f122])).
% 10.38/1.76  fof(f75,plain,(
% 10.38/1.76    ( ! [X4,X0] : (k4_tarski(sK6(X4),sK7(X4)) = X4 | ~r2_hidden(X4,X0) | ~v1_relat_1(X0)) )),
% 10.38/1.76    inference(cnf_transformation,[],[f48])).
% 10.38/1.76  fof(f48,plain,(
% 10.38/1.76    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK5(X0) & r2_hidden(sK5(X0),X0))) & (! [X4] : (k4_tarski(sK6(X4),sK7(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 10.38/1.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f45,f47,f46])).
% 10.38/1.76  fof(f46,plain,(
% 10.38/1.76    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK5(X0) & r2_hidden(sK5(X0),X0)))),
% 10.38/1.76    introduced(choice_axiom,[])).
% 10.38/1.76  fof(f47,plain,(
% 10.38/1.76    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK6(X4),sK7(X4)) = X4)),
% 10.38/1.76    introduced(choice_axiom,[])).
% 10.38/1.76  fof(f45,plain,(
% 10.38/1.76    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 10.38/1.76    inference(rectify,[],[f44])).
% 10.38/1.76  fof(f44,plain,(
% 10.38/1.76    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 10.38/1.76    inference(nnf_transformation,[],[f24])).
% 10.38/1.76  fof(f24,plain,(
% 10.38/1.76    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 10.38/1.76    inference(ennf_transformation,[],[f13])).
% 10.38/1.76  fof(f13,axiom,(
% 10.38/1.76    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 10.38/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 10.38/1.76  fof(f215,plain,(
% 10.38/1.76    r2_hidden(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~spl16_9),
% 10.38/1.76    inference(avatar_component_clause,[],[f213])).
% 10.38/1.76  fof(f737,plain,(
% 10.38/1.76    ~spl16_11 | spl16_54 | ~spl16_10),
% 10.38/1.76    inference(avatar_split_clause,[],[f731,f218,f734,f247])).
% 10.38/1.76  fof(f247,plain,(
% 10.38/1.76    spl16_11 <=> v1_relat_1(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),
% 10.38/1.76    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).
% 10.38/1.76  fof(f731,plain,(
% 10.38/1.76    sQ15_eqProxy(k4_tarski(sK6(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK7(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))))),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))) | ~v1_relat_1(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~spl16_10),
% 10.38/1.76    inference(resolution,[],[f220,f128])).
% 10.38/1.76  fof(f220,plain,(
% 10.38/1.76    r2_hidden(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~spl16_10),
% 10.38/1.76    inference(avatar_component_clause,[],[f218])).
% 10.38/1.76  fof(f673,plain,(
% 10.38/1.76    spl16_30),
% 10.38/1.76    inference(avatar_contradiction_clause,[],[f669])).
% 10.38/1.76  fof(f669,plain,(
% 10.38/1.76    $false | spl16_30),
% 10.38/1.76    inference(resolution,[],[f466,f141])).
% 10.38/1.76  fof(f466,plain,(
% 10.38/1.76    ~v1_relat_1(k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | spl16_30),
% 10.38/1.76    inference(avatar_component_clause,[],[f464])).
% 10.38/1.76  fof(f599,plain,(
% 10.38/1.76    spl16_37 | ~spl16_8),
% 10.38/1.76    inference(avatar_split_clause,[],[f584,f208,f537])).
% 10.38/1.76  fof(f584,plain,(
% 10.38/1.76    r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0)) | ~spl16_8),
% 10.38/1.76    inference(resolution,[],[f209,f121])).
% 10.38/1.76  fof(f476,plain,(
% 10.38/1.76    ~spl16_1 | ~spl16_30 | spl16_32 | ~spl16_7),
% 10.38/1.76    inference(avatar_split_clause,[],[f452,f204,f473,f464,f171])).
% 10.38/1.76  fof(f452,plain,(
% 10.38/1.76    r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),sK2) | ~v1_relat_1(k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~v1_relat_1(sK2) | ~spl16_7),
% 10.38/1.76    inference(resolution,[],[f205,f117])).
% 10.38/1.76  fof(f117,plain,(
% 10.38/1.76    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 10.38/1.76    inference(equality_resolution,[],[f70])).
% 10.38/1.76  fof(f70,plain,(
% 10.38/1.76    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 10.38/1.76    inference(cnf_transformation,[],[f43])).
% 10.38/1.76  fof(f205,plain,(
% 10.38/1.76    r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~spl16_7),
% 10.38/1.76    inference(avatar_component_clause,[],[f204])).
% 10.38/1.76  fof(f471,plain,(
% 10.38/1.76    ~spl16_1 | ~spl16_30 | spl16_31 | ~spl16_7),
% 10.38/1.76    inference(avatar_split_clause,[],[f451,f204,f468,f464,f171])).
% 10.38/1.76  fof(f451,plain,(
% 10.38/1.76    r2_hidden(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(sK0,sK1)) | ~v1_relat_1(k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~v1_relat_1(sK2) | ~spl16_7),
% 10.38/1.76    inference(resolution,[],[f205,f118])).
% 10.38/1.76  fof(f299,plain,(
% 10.38/1.76    spl16_11),
% 10.38/1.76    inference(avatar_contradiction_clause,[],[f295])).
% 10.38/1.76  fof(f295,plain,(
% 10.38/1.76    $false | spl16_11),
% 10.38/1.76    inference(resolution,[],[f265,f141])).
% 10.38/1.76  fof(f265,plain,(
% 10.38/1.76    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl16_11),
% 10.38/1.76    inference(resolution,[],[f249,f109])).
% 10.38/1.76  fof(f109,plain,(
% 10.38/1.76    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 10.38/1.76    inference(definition_unfolding,[],[f83,f79])).
% 10.38/1.76  fof(f83,plain,(
% 10.38/1.76    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 10.38/1.76    inference(cnf_transformation,[],[f26])).
% 10.38/1.76  fof(f26,plain,(
% 10.38/1.76    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 10.38/1.76    inference(ennf_transformation,[],[f15])).
% 10.38/1.76  fof(f15,axiom,(
% 10.38/1.76    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 10.38/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).
% 10.38/1.76  fof(f249,plain,(
% 10.38/1.76    ~v1_relat_1(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | spl16_11),
% 10.38/1.76    inference(avatar_component_clause,[],[f247])).
% 10.38/1.76  fof(f245,plain,(
% 10.38/1.76    spl16_1),
% 10.38/1.76    inference(avatar_contradiction_clause,[],[f242])).
% 10.38/1.76  fof(f242,plain,(
% 10.38/1.76    $false | spl16_1),
% 10.38/1.76    inference(resolution,[],[f173,f66])).
% 10.38/1.76  fof(f173,plain,(
% 10.38/1.76    ~v1_relat_1(sK2) | spl16_1),
% 10.38/1.76    inference(avatar_component_clause,[],[f171])).
% 10.38/1.76  fof(f226,plain,(
% 10.38/1.76    spl16_9 | spl16_10 | spl16_7 | spl16_8),
% 10.38/1.76    inference(avatar_split_clause,[],[f196,f208,f204,f218,f213])).
% 10.38/1.76  fof(f196,plain,(
% 10.38/1.76    r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | r2_hidden(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | r2_hidden(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 10.38/1.76    inference(resolution,[],[f123,f136])).
% 10.38/1.76  fof(f136,plain,(
% 10.38/1.76    ( ! [X0,X1] : (sQ15_eqProxy(X0,X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | r2_hidden(sK11(X1),X1) | r2_hidden(sK12(X0),X0)) )),
% 10.38/1.76    inference(equality_proxy_replacement,[],[f87,f122])).
% 10.38/1.76  fof(f87,plain,(
% 10.38/1.76    ( ! [X0,X1] : (X0 = X1 | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | r2_hidden(sK11(X1),X1) | r2_hidden(sK12(X0),X0)) )),
% 10.38/1.76    inference(cnf_transformation,[],[f55])).
% 10.38/1.76  fof(f225,plain,(
% 10.38/1.76    spl16_5 | spl16_10 | spl16_7 | spl16_8),
% 10.38/1.76    inference(avatar_split_clause,[],[f195,f208,f204,f218,f198])).
% 10.38/1.76  fof(f195,plain,(
% 10.38/1.76    ( ! [X14,X15] : (r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | r2_hidden(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~sQ15_eqProxy(k4_tarski(X14,X15),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))) )),
% 10.38/1.76    inference(resolution,[],[f123,f135])).
% 10.38/1.76  fof(f135,plain,(
% 10.38/1.76    ( ! [X0,X8,X1,X9] : (sQ15_eqProxy(X0,X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | r2_hidden(sK11(X1),X1) | ~sQ15_eqProxy(k4_tarski(X8,X9),sK12(X0))) )),
% 10.38/1.76    inference(equality_proxy_replacement,[],[f88,f122,f122])).
% 10.38/1.76  fof(f88,plain,(
% 10.38/1.76    ( ! [X0,X8,X1,X9] : (X0 = X1 | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | r2_hidden(sK11(X1),X1) | k4_tarski(X8,X9) != sK12(X0)) )),
% 10.38/1.76    inference(cnf_transformation,[],[f55])).
% 10.38/1.76  fof(f224,plain,(
% 10.38/1.76    spl16_9 | spl16_6 | spl16_7 | spl16_8),
% 10.38/1.76    inference(avatar_split_clause,[],[f194,f208,f204,f201,f213])).
% 10.38/1.76  fof(f194,plain,(
% 10.38/1.76    ( ! [X12,X13] : (r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~sQ15_eqProxy(k4_tarski(X12,X13),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))) | r2_hidden(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))) )),
% 10.38/1.76    inference(resolution,[],[f123,f134])).
% 10.38/1.76  fof(f134,plain,(
% 10.38/1.76    ( ! [X6,X0,X5,X1] : (sQ15_eqProxy(X0,X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | ~sQ15_eqProxy(k4_tarski(X5,X6),sK11(X1)) | r2_hidden(sK12(X0),X0)) )),
% 10.38/1.76    inference(equality_proxy_replacement,[],[f89,f122,f122])).
% 10.38/1.76  fof(f89,plain,(
% 10.38/1.76    ( ! [X6,X0,X5,X1] : (X0 = X1 | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | k4_tarski(X5,X6) != sK11(X1) | r2_hidden(sK12(X0),X0)) )),
% 10.38/1.76    inference(cnf_transformation,[],[f55])).
% 10.38/1.76  fof(f223,plain,(
% 10.38/1.76    spl16_5 | spl16_6 | spl16_7 | spl16_8),
% 10.38/1.76    inference(avatar_split_clause,[],[f193,f208,f204,f201,f198])).
% 10.38/1.76  fof(f193,plain,(
% 10.38/1.76    ( ! [X10,X8,X11,X9] : (r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~sQ15_eqProxy(k4_tarski(X8,X9),sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))) | ~sQ15_eqProxy(k4_tarski(X10,X11),sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))))) )),
% 10.38/1.76    inference(resolution,[],[f123,f133])).
% 10.38/1.76  fof(f133,plain,(
% 10.38/1.76    ( ! [X6,X0,X8,X5,X1,X9] : (sQ15_eqProxy(X0,X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | ~sQ15_eqProxy(k4_tarski(X5,X6),sK11(X1)) | ~sQ15_eqProxy(k4_tarski(X8,X9),sK12(X0))) )),
% 10.38/1.76    inference(equality_proxy_replacement,[],[f90,f122,f122,f122])).
% 10.38/1.76  fof(f90,plain,(
% 10.38/1.76    ( ! [X6,X0,X8,X5,X1,X9] : (X0 = X1 | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | k4_tarski(X5,X6) != sK11(X1) | k4_tarski(X8,X9) != sK12(X0)) )),
% 10.38/1.76    inference(cnf_transformation,[],[f55])).
% 10.38/1.76  fof(f222,plain,(
% 10.38/1.76    spl16_9 | spl16_10 | ~spl16_7 | ~spl16_8),
% 10.38/1.76    inference(avatar_split_clause,[],[f192,f208,f204,f218,f213])).
% 10.38/1.76  fof(f192,plain,(
% 10.38/1.76    ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | ~r2_hidden(k4_tarski(sK9(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),sK10(k7_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)))),k7_relat_1(sK2,k6_subset_1(sK0,sK1))) | r2_hidden(sK11(k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),k6_subset_1(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))) | r2_hidden(sK12(k7_relat_1(sK2,k6_subset_1(sK0,sK1))),k7_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 10.38/1.76    inference(resolution,[],[f123,f132])).
% 10.38/1.76  fof(f132,plain,(
% 10.38/1.76    ( ! [X0,X1] : (sQ15_eqProxy(X0,X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | r2_hidden(sK11(X1),X1) | r2_hidden(sK12(X0),X0)) )),
% 10.38/1.76    inference(equality_proxy_replacement,[],[f91,f122])).
% 10.38/1.76  fof(f91,plain,(
% 10.38/1.76    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | r2_hidden(sK11(X1),X1) | r2_hidden(sK12(X0),X0)) )),
% 10.38/1.76    inference(cnf_transformation,[],[f55])).
% 10.38/1.76  fof(f185,plain,(
% 10.38/1.76    ~spl16_1 | spl16_4),
% 10.38/1.76    inference(avatar_split_clause,[],[f156,f183,f171])).
% 10.38/1.76  fof(f156,plain,(
% 10.38/1.76    ( ! [X6,X8,X7] : (r2_hidden(k4_tarski(X6,X7),k7_relat_1(sK2,X8)) | ~r2_hidden(k4_tarski(X6,X7),sK2) | ~r2_hidden(X6,X8) | ~v1_relat_1(sK2)) )),
% 10.38/1.76    inference(resolution,[],[f141,f116])).
% 10.38/1.76  fof(f177,plain,(
% 10.38/1.76    ~spl16_1 | spl16_2),
% 10.38/1.76    inference(avatar_split_clause,[],[f154,f175,f171])).
% 10.38/1.76  fof(f154,plain,(
% 10.38/1.76    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(k4_tarski(X0,X2),k7_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 10.38/1.76    inference(resolution,[],[f141,f118])).
% 10.38/1.76  % SZS output end Proof for theBenchmark
% 10.38/1.76  % (25434)------------------------------
% 10.38/1.76  % (25434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.38/1.76  % (25434)Termination reason: Refutation
% 10.38/1.76  
% 10.38/1.76  % (25434)Memory used [KB]: 12409
% 10.38/1.76  % (25434)Time elapsed: 1.229 s
% 10.38/1.76  % (25434)------------------------------
% 10.38/1.76  % (25434)------------------------------
% 10.38/1.76  % (25418)Success in time 1.386 s
%------------------------------------------------------------------------------
