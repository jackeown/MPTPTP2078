%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0481+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:32 EST 2020

% Result     : Theorem 19.53s
% Output     : Refutation 19.53s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 151 expanded)
%              Number of leaves         :   16 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  230 ( 474 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33061,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3670,f6738,f6951,f16088,f16090,f19306,f25735,f27847,f33019])).

fof(f33019,plain,
    ( ~ spl177_45
    | spl177_46 ),
    inference(avatar_contradiction_clause,[],[f33018])).

fof(f33018,plain,
    ( $false
    | ~ spl177_45
    | spl177_46 ),
    inference(subsumption_resolution,[],[f33017,f1673])).

fof(f1673,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f1263])).

fof(f1263,plain,
    ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK10),sK11),sK11)
      | ~ r1_tarski(k5_relat_1(sK11,k6_relat_1(sK10)),sK11) )
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f734,f1262])).

fof(f1262,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK10),sK11),sK11)
        | ~ r1_tarski(k5_relat_1(sK11,k6_relat_1(sK10)),sK11) )
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f734,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f721])).

fof(f721,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f720])).

fof(f720,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f33017,plain,
    ( ~ v1_relat_1(sK11)
    | ~ spl177_45
    | spl177_46 ),
    inference(subsumption_resolution,[],[f32870,f4220])).

fof(f4220,plain,
    ( ~ r2_hidden(k4_tarski(sK26(k5_relat_1(k6_relat_1(sK10),sK11),sK11),sK27(k5_relat_1(k6_relat_1(sK10),sK11),sK11)),sK11)
    | spl177_46 ),
    inference(avatar_component_clause,[],[f4218])).

fof(f4218,plain,
    ( spl177_46
  <=> r2_hidden(k4_tarski(sK26(k5_relat_1(k6_relat_1(sK10),sK11),sK11),sK27(k5_relat_1(k6_relat_1(sK10),sK11),sK11)),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl177_46])])).

fof(f32870,plain,
    ( r2_hidden(k4_tarski(sK26(k5_relat_1(k6_relat_1(sK10),sK11),sK11),sK27(k5_relat_1(k6_relat_1(sK10),sK11),sK11)),sK11)
    | ~ v1_relat_1(sK11)
    | ~ spl177_45 ),
    inference(resolution,[],[f4215,f2573])).

fof(f2573,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1584])).

fof(f1584,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f1583])).

fof(f1583,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f1193])).

fof(f1193,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f718])).

fof(f718,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

fof(f4215,plain,
    ( r2_hidden(k4_tarski(sK26(k5_relat_1(k6_relat_1(sK10),sK11),sK11),sK27(k5_relat_1(k6_relat_1(sK10),sK11),sK11)),k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ spl177_45 ),
    inference(avatar_component_clause,[],[f4213])).

fof(f4213,plain,
    ( spl177_45
  <=> r2_hidden(k4_tarski(sK26(k5_relat_1(k6_relat_1(sK10),sK11),sK11),sK27(k5_relat_1(k6_relat_1(sK10),sK11),sK11)),k5_relat_1(k6_relat_1(sK10),sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl177_45])])).

fof(f27847,plain,
    ( spl177_19
    | ~ spl177_18 ),
    inference(avatar_split_clause,[],[f27651,f3911,f3916])).

fof(f3916,plain,
    ( spl177_19
  <=> r2_hidden(k4_tarski(sK26(k5_relat_1(sK11,k6_relat_1(sK10)),sK11),sK27(k5_relat_1(sK11,k6_relat_1(sK10)),sK11)),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl177_19])])).

fof(f3911,plain,
    ( spl177_18
  <=> r2_hidden(k4_tarski(sK26(k5_relat_1(sK11,k6_relat_1(sK10)),sK11),sK27(k5_relat_1(sK11,k6_relat_1(sK10)),sK11)),k5_relat_1(sK11,k6_relat_1(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl177_18])])).

fof(f27651,plain,
    ( r2_hidden(k4_tarski(sK26(k5_relat_1(sK11,k6_relat_1(sK10)),sK11),sK27(k5_relat_1(sK11,k6_relat_1(sK10)),sK11)),sK11)
    | ~ spl177_18 ),
    inference(resolution,[],[f3913,f3735])).

fof(f3735,plain,(
    ! [X88,X87,X89] :
      ( ~ r2_hidden(k4_tarski(X87,X88),k5_relat_1(sK11,k6_relat_1(X89)))
      | r2_hidden(k4_tarski(X87,X88),sK11) ) ),
    inference(resolution,[],[f1673,f2570])).

fof(f2570,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1582])).

fof(f1582,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f1581])).

fof(f1581,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f1192])).

fof(f1192,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f719])).

fof(f719,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

fof(f3913,plain,
    ( r2_hidden(k4_tarski(sK26(k5_relat_1(sK11,k6_relat_1(sK10)),sK11),sK27(k5_relat_1(sK11,k6_relat_1(sK10)),sK11)),k5_relat_1(sK11,k6_relat_1(sK10)))
    | ~ spl177_18 ),
    inference(avatar_component_clause,[],[f3911])).

fof(f25735,plain,
    ( spl177_45
    | spl177_2
    | ~ spl177_44 ),
    inference(avatar_split_clause,[],[f25734,f4209,f3667,f4213])).

fof(f3667,plain,
    ( spl177_2
  <=> r1_tarski(k5_relat_1(k6_relat_1(sK10),sK11),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl177_2])])).

fof(f4209,plain,
    ( spl177_44
  <=> v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl177_44])])).

fof(f25734,plain,
    ( r2_hidden(k4_tarski(sK26(k5_relat_1(k6_relat_1(sK10),sK11),sK11),sK27(k5_relat_1(k6_relat_1(sK10),sK11),sK11)),k5_relat_1(k6_relat_1(sK10),sK11))
    | spl177_2
    | ~ spl177_44 ),
    inference(subsumption_resolution,[],[f25702,f4210])).

fof(f4210,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ spl177_44 ),
    inference(avatar_component_clause,[],[f4209])).

fof(f25702,plain,
    ( r2_hidden(k4_tarski(sK26(k5_relat_1(k6_relat_1(sK10),sK11),sK11),sK27(k5_relat_1(k6_relat_1(sK10),sK11),sK11)),k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11))
    | spl177_2 ),
    inference(resolution,[],[f3669,f1807])).

fof(f1807,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK26(X0,X1),sK27(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1292])).

fof(f1292,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK26(X0,X1),sK27(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK26(X0,X1),sK27(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26,sK27])],[f1290,f1291])).

fof(f1291,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK26(X0,X1),sK27(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK26(X0,X1),sK27(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1290,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1289])).

fof(f1289,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f801])).

fof(f801,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f643])).

fof(f643,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f3669,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK10),sK11),sK11)
    | spl177_2 ),
    inference(avatar_component_clause,[],[f3667])).

fof(f19306,plain,
    ( ~ spl177_46
    | spl177_2
    | ~ spl177_44 ),
    inference(avatar_split_clause,[],[f19305,f4209,f3667,f4218])).

fof(f19305,plain,
    ( ~ r2_hidden(k4_tarski(sK26(k5_relat_1(k6_relat_1(sK10),sK11),sK11),sK27(k5_relat_1(k6_relat_1(sK10),sK11),sK11)),sK11)
    | spl177_2
    | ~ spl177_44 ),
    inference(subsumption_resolution,[],[f19272,f4210])).

fof(f19272,plain,
    ( ~ r2_hidden(k4_tarski(sK26(k5_relat_1(k6_relat_1(sK10),sK11),sK11),sK27(k5_relat_1(k6_relat_1(sK10),sK11),sK11)),sK11)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11))
    | spl177_2 ),
    inference(resolution,[],[f3669,f1808])).

fof(f1808,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK26(X0,X1),sK27(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1292])).

fof(f16090,plain,
    ( ~ spl177_19
    | spl177_1
    | ~ spl177_17 ),
    inference(avatar_split_clause,[],[f16089,f3907,f3663,f3916])).

fof(f3663,plain,
    ( spl177_1
  <=> r1_tarski(k5_relat_1(sK11,k6_relat_1(sK10)),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl177_1])])).

fof(f3907,plain,
    ( spl177_17
  <=> v1_relat_1(k5_relat_1(sK11,k6_relat_1(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl177_17])])).

fof(f16089,plain,
    ( ~ r2_hidden(k4_tarski(sK26(k5_relat_1(sK11,k6_relat_1(sK10)),sK11),sK27(k5_relat_1(sK11,k6_relat_1(sK10)),sK11)),sK11)
    | spl177_1
    | ~ spl177_17 ),
    inference(subsumption_resolution,[],[f16056,f3908])).

fof(f3908,plain,
    ( v1_relat_1(k5_relat_1(sK11,k6_relat_1(sK10)))
    | ~ spl177_17 ),
    inference(avatar_component_clause,[],[f3907])).

fof(f16056,plain,
    ( ~ r2_hidden(k4_tarski(sK26(k5_relat_1(sK11,k6_relat_1(sK10)),sK11),sK27(k5_relat_1(sK11,k6_relat_1(sK10)),sK11)),sK11)
    | ~ v1_relat_1(k5_relat_1(sK11,k6_relat_1(sK10)))
    | spl177_1 ),
    inference(resolution,[],[f3665,f1808])).

fof(f3665,plain,
    ( ~ r1_tarski(k5_relat_1(sK11,k6_relat_1(sK10)),sK11)
    | spl177_1 ),
    inference(avatar_component_clause,[],[f3663])).

fof(f16088,plain,
    ( spl177_18
    | spl177_1
    | ~ spl177_17 ),
    inference(avatar_split_clause,[],[f16087,f3907,f3663,f3911])).

fof(f16087,plain,
    ( r2_hidden(k4_tarski(sK26(k5_relat_1(sK11,k6_relat_1(sK10)),sK11),sK27(k5_relat_1(sK11,k6_relat_1(sK10)),sK11)),k5_relat_1(sK11,k6_relat_1(sK10)))
    | spl177_1
    | ~ spl177_17 ),
    inference(subsumption_resolution,[],[f16055,f3908])).

fof(f16055,plain,
    ( r2_hidden(k4_tarski(sK26(k5_relat_1(sK11,k6_relat_1(sK10)),sK11),sK27(k5_relat_1(sK11,k6_relat_1(sK10)),sK11)),k5_relat_1(sK11,k6_relat_1(sK10)))
    | ~ v1_relat_1(k5_relat_1(sK11,k6_relat_1(sK10)))
    | spl177_1 ),
    inference(resolution,[],[f3665,f1807])).

fof(f6951,plain,(
    spl177_44 ),
    inference(avatar_contradiction_clause,[],[f6950])).

fof(f6950,plain,
    ( $false
    | spl177_44 ),
    inference(subsumption_resolution,[],[f6949,f1690])).

fof(f1690,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f654])).

fof(f654,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f6949,plain,
    ( ~ v1_relat_1(k6_relat_1(sK10))
    | spl177_44 ),
    inference(subsumption_resolution,[],[f6943,f1673])).

fof(f6943,plain,
    ( ~ v1_relat_1(sK11)
    | ~ v1_relat_1(k6_relat_1(sK10))
    | spl177_44 ),
    inference(resolution,[],[f4211,f2128])).

fof(f2128,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1009])).

fof(f1009,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1008])).

fof(f1008,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f653])).

fof(f653,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f4211,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11))
    | spl177_44 ),
    inference(avatar_component_clause,[],[f4209])).

fof(f6738,plain,(
    spl177_17 ),
    inference(avatar_contradiction_clause,[],[f6737])).

fof(f6737,plain,
    ( $false
    | spl177_17 ),
    inference(subsumption_resolution,[],[f6736,f1673])).

fof(f6736,plain,
    ( ~ v1_relat_1(sK11)
    | spl177_17 ),
    inference(subsumption_resolution,[],[f6730,f1690])).

fof(f6730,plain,
    ( ~ v1_relat_1(k6_relat_1(sK10))
    | ~ v1_relat_1(sK11)
    | spl177_17 ),
    inference(resolution,[],[f3909,f2128])).

fof(f3909,plain,
    ( ~ v1_relat_1(k5_relat_1(sK11,k6_relat_1(sK10)))
    | spl177_17 ),
    inference(avatar_component_clause,[],[f3907])).

fof(f3670,plain,
    ( ~ spl177_1
    | ~ spl177_2 ),
    inference(avatar_split_clause,[],[f1674,f3667,f3663])).

fof(f1674,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK10),sK11),sK11)
    | ~ r1_tarski(k5_relat_1(sK11,k6_relat_1(sK10)),sK11) ),
    inference(cnf_transformation,[],[f1263])).
%------------------------------------------------------------------------------
