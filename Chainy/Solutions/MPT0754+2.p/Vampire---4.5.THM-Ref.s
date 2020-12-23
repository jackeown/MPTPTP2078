%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0754+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   32 (  78 expanded)
%              Number of leaves         :    5 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 625 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1258,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1253,f1222])).

fof(f1222,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f1212,f1144])).

fof(f1144,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1134])).

fof(f1134,plain,
    ( ( ~ v5_ordinal1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v5_relat_1(sK2,sK1)
      | ~ v1_relat_1(sK2) )
    & v5_ordinal1(sK2)
    & v1_funct_1(sK2)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1114,f1133,f1132])).

fof(f1132,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ v5_ordinal1(X2)
              | ~ v1_funct_1(X2)
              | ~ v5_relat_1(X2,X1)
              | ~ v1_relat_1(X2) )
            & v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,sK1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1133,plain,
    ( ? [X2] :
        ( ( ~ v5_ordinal1(X2)
          | ~ v1_funct_1(X2)
          | ~ v5_relat_1(X2,sK1)
          | ~ v1_relat_1(X2) )
        & v5_ordinal1(X2)
        & v1_funct_1(X2)
        & v5_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ( ~ v5_ordinal1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v5_relat_1(sK2,sK1)
        | ~ v1_relat_1(sK2) )
      & v5_ordinal1(sK2)
      & v1_funct_1(sK2)
      & v5_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1114,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1113])).

fof(f1113,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1107])).

fof(f1107,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v5_ordinal1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( v5_ordinal1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X1)
              & v1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f1106])).

fof(f1106,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X1)
            & v1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_ordinal1)).

fof(f1212,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1145,f1172])).

fof(f1172,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1140])).

fof(f1140,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1129])).

fof(f1129,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f1145,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f1134])).

fof(f1253,plain,(
    ~ r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(resolution,[],[f1203,f1233])).

fof(f1233,plain,(
    ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f1232,f1144])).

fof(f1232,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f1231,f1147])).

fof(f1147,plain,(
    v5_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f1134])).

fof(f1231,plain,
    ( ~ v5_ordinal1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f1230,f1146])).

fof(f1146,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1134])).

fof(f1230,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v5_ordinal1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f1226])).

fof(f1226,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v5_ordinal1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1148,f1173])).

fof(f1173,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1140])).

fof(f1148,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v5_ordinal1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1134])).

fof(f1203,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK1)
      | ~ r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f1143,f1174])).

fof(f1174,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1131])).

fof(f1131,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1130])).

fof(f1130,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1143,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f1134])).
%------------------------------------------------------------------------------
