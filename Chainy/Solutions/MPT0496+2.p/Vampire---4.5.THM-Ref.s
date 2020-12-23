%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0496+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:33 EST 2020

% Result     : Theorem 16.73s
% Output     : Refutation 16.73s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 252 expanded)
%              Number of leaves         :   16 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  389 ( 928 expanded)
%              Number of equality atoms :   31 ( 141 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10892)Time limit reached!
% (10892)------------------------------
% (10892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10892)Termination reason: Time limit

% (10892)Memory used [KB]: 17014
% (10892)Time elapsed: 1.234 s
% (10892)------------------------------
% (10892)------------------------------
fof(f26860,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f7136,f25018,f25029,f26505,f26507,f26705,f26710,f26713,f26846])).

fof(f26846,plain,
    ( ~ spl179_881
    | ~ spl179_882
    | spl179_39 ),
    inference(avatar_split_clause,[],[f26845,f4229,f25026,f25022])).

fof(f25022,plain,
    ( spl179_881
  <=> r2_hidden(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl179_881])])).

fof(f25026,plain,
    ( spl179_882
  <=> r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl179_882])])).

fof(f4229,plain,
    ( spl179_39
  <=> r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k5_relat_1(k6_relat_1(sK10),sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl179_39])])).

fof(f26845,plain,
    ( ~ r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),sK11)
    | ~ r2_hidden(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK10)
    | spl179_39 ),
    inference(subsumption_resolution,[],[f26741,f1720])).

fof(f1720,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f1303])).

fof(f1303,plain,
    ( k5_relat_1(k6_relat_1(sK10),sK11) != k7_relat_1(sK11,sK10)
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f752,f1302])).

fof(f1302,plain,
    ( ? [X0,X1] :
        ( k5_relat_1(k6_relat_1(X0),X1) != k7_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( k5_relat_1(k6_relat_1(sK10),sK11) != k7_relat_1(sK11,sK10)
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f752,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != k7_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f739])).

fof(f739,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(negated_conjecture,[],[f738])).

fof(f738,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f26741,plain,
    ( ~ r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),sK11)
    | ~ r2_hidden(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK10)
    | ~ v1_relat_1(sK11)
    | spl179_39 ),
    inference(resolution,[],[f4231,f2648])).

fof(f2648,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1631])).

fof(f1631,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f1630])).

fof(f1630,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f1233])).

fof(f1233,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f721])).

fof(f721,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

fof(f4231,plain,
    ( ~ r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k5_relat_1(k6_relat_1(sK10),sK11))
    | spl179_39 ),
    inference(avatar_component_clause,[],[f4229])).

fof(f26713,plain,
    ( spl179_882
    | ~ spl179_40 ),
    inference(avatar_split_clause,[],[f26712,f4233,f25026])).

fof(f4233,plain,
    ( spl179_40
  <=> r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k7_relat_1(sK11,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl179_40])])).

fof(f26712,plain,
    ( r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),sK11)
    | ~ spl179_40 ),
    inference(subsumption_resolution,[],[f26711,f1720])).

fof(f26711,plain,
    ( r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),sK11)
    | ~ v1_relat_1(sK11)
    | ~ spl179_40 ),
    inference(subsumption_resolution,[],[f26557,f3796])).

fof(f3796,plain,(
    ! [X62] : v1_relat_1(k7_relat_1(sK11,X62)) ),
    inference(resolution,[],[f1720,f2009])).

fof(f2009,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f861])).

fof(f861,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f26557,plain,
    ( r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),sK11)
    | ~ v1_relat_1(k7_relat_1(sK11,sK10))
    | ~ v1_relat_1(sK11)
    | ~ spl179_40 ),
    inference(resolution,[],[f4234,f2891])).

fof(f2891,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1860])).

fof(f1860,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1337])).

fof(f1337,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK28(X0,X1,X2),sK29(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK28(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK28(X0,X1,X2),sK29(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK28(X0,X1,X2),sK29(X0,X1,X2)),X0)
                    & r2_hidden(sK28(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK28(X0,X1,X2),sK29(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29])],[f1335,f1336])).

fof(f1336,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK28(X0,X1,X2),sK29(X0,X1,X2)),X0)
          | ~ r2_hidden(sK28(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK28(X0,X1,X2),sK29(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK28(X0,X1,X2),sK29(X0,X1,X2)),X0)
            & r2_hidden(sK28(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK28(X0,X1,X2),sK29(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1335,plain,(
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
    inference(rectify,[],[f1334])).

fof(f1334,plain,(
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
    inference(flattening,[],[f1333])).

fof(f1333,plain,(
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
    inference(nnf_transformation,[],[f822])).

fof(f822,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f641])).

fof(f641,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f4234,plain,
    ( r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k7_relat_1(sK11,sK10))
    | ~ spl179_40 ),
    inference(avatar_component_clause,[],[f4233])).

fof(f26710,plain,
    ( spl179_881
    | ~ spl179_40 ),
    inference(avatar_split_clause,[],[f26709,f4233,f25022])).

fof(f26709,plain,
    ( r2_hidden(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK10)
    | ~ spl179_40 ),
    inference(subsumption_resolution,[],[f26708,f1720])).

fof(f26708,plain,
    ( r2_hidden(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK10)
    | ~ v1_relat_1(sK11)
    | ~ spl179_40 ),
    inference(subsumption_resolution,[],[f26556,f3796])).

fof(f26556,plain,
    ( r2_hidden(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK10)
    | ~ v1_relat_1(k7_relat_1(sK11,sK10))
    | ~ v1_relat_1(sK11)
    | ~ spl179_40 ),
    inference(resolution,[],[f4234,f2892])).

fof(f2892,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1859])).

fof(f1859,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1337])).

fof(f26705,plain,
    ( ~ spl179_39
    | ~ spl179_38
    | ~ spl179_40 ),
    inference(avatar_split_clause,[],[f26704,f4233,f4225,f4229])).

fof(f4225,plain,
    ( spl179_38
  <=> v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl179_38])])).

fof(f26704,plain,
    ( ~ r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ spl179_38
    | ~ spl179_40 ),
    inference(subsumption_resolution,[],[f26703,f4226])).

fof(f4226,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ spl179_38 ),
    inference(avatar_component_clause,[],[f4225])).

fof(f26703,plain,
    ( ~ r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ spl179_40 ),
    inference(subsumption_resolution,[],[f26702,f3796])).

fof(f26702,plain,
    ( ~ r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ v1_relat_1(k7_relat_1(sK11,sK10))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ spl179_40 ),
    inference(subsumption_resolution,[],[f26553,f3144])).

fof(f3144,plain,(
    ~ sQ178_eqProxy(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)) ),
    inference(equality_proxy_replacement,[],[f1721,f3108])).

fof(f3108,plain,(
    ! [X1,X0] :
      ( sQ178_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ178_eqProxy])])).

fof(f1721,plain,(
    k5_relat_1(k6_relat_1(sK10),sK11) != k7_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f1303])).

fof(f26553,plain,
    ( sQ178_eqProxy(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))
    | ~ r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ v1_relat_1(k7_relat_1(sK11,sK10))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ spl179_40 ),
    inference(resolution,[],[f4234,f3199])).

fof(f3199,plain,(
    ! [X0,X1] :
      ( sQ178_eqProxy(X0,X1)
      | ~ r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1837,f3108])).

fof(f1837,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1318])).

fof(f1318,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19])],[f1316,f1317])).

fof(f1317,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1316,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1315])).

fof(f1315,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f807])).

fof(f807,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f643])).

fof(f643,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).

fof(f26507,plain,
    ( spl179_882
    | ~ spl179_39 ),
    inference(avatar_split_clause,[],[f26506,f4229,f25026])).

fof(f26506,plain,
    ( r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),sK11)
    | ~ spl179_39 ),
    inference(subsumption_resolution,[],[f26353,f1720])).

fof(f26353,plain,
    ( r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),sK11)
    | ~ v1_relat_1(sK11)
    | ~ spl179_39 ),
    inference(resolution,[],[f4230,f2647])).

fof(f2647,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1631])).

fof(f4230,plain,
    ( r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ spl179_39 ),
    inference(avatar_component_clause,[],[f4229])).

fof(f26505,plain,
    ( spl179_881
    | ~ spl179_39 ),
    inference(avatar_split_clause,[],[f26504,f4229,f25022])).

fof(f26504,plain,
    ( r2_hidden(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK10)
    | ~ spl179_39 ),
    inference(subsumption_resolution,[],[f26352,f1720])).

fof(f26352,plain,
    ( r2_hidden(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK10)
    | ~ v1_relat_1(sK11)
    | ~ spl179_39 ),
    inference(resolution,[],[f4230,f2646])).

fof(f2646,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1631])).

fof(f25029,plain,
    ( ~ spl179_881
    | ~ spl179_882
    | spl179_40 ),
    inference(avatar_split_clause,[],[f25020,f4233,f25026,f25022])).

fof(f25020,plain,
    ( ~ r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),sK11)
    | ~ r2_hidden(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK10)
    | spl179_40 ),
    inference(subsumption_resolution,[],[f25019,f1720])).

fof(f25019,plain,
    ( ~ r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),sK11)
    | ~ r2_hidden(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK10)
    | ~ v1_relat_1(sK11)
    | spl179_40 ),
    inference(subsumption_resolution,[],[f24912,f3796])).

fof(f24912,plain,
    ( ~ r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),sK11)
    | ~ r2_hidden(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK10)
    | ~ v1_relat_1(k7_relat_1(sK11,sK10))
    | ~ v1_relat_1(sK11)
    | spl179_40 ),
    inference(resolution,[],[f4235,f2890])).

fof(f2890,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1861])).

fof(f1861,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1337])).

fof(f4235,plain,
    ( ~ r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k7_relat_1(sK11,sK10))
    | spl179_40 ),
    inference(avatar_component_clause,[],[f4233])).

fof(f25018,plain,
    ( spl179_39
    | ~ spl179_38
    | spl179_40 ),
    inference(avatar_split_clause,[],[f25017,f4233,f4225,f4229])).

fof(f25017,plain,
    ( r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ spl179_38
    | spl179_40 ),
    inference(subsumption_resolution,[],[f25016,f4226])).

fof(f25016,plain,
    ( r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11))
    | spl179_40 ),
    inference(subsumption_resolution,[],[f25015,f3796])).

fof(f25015,plain,
    ( r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ v1_relat_1(k7_relat_1(sK11,sK10))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11))
    | spl179_40 ),
    inference(subsumption_resolution,[],[f24911,f3144])).

fof(f24911,plain,
    ( sQ178_eqProxy(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))
    | r2_hidden(k4_tarski(sK18(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10)),sK19(k5_relat_1(k6_relat_1(sK10),sK11),k7_relat_1(sK11,sK10))),k5_relat_1(k6_relat_1(sK10),sK11))
    | ~ v1_relat_1(k7_relat_1(sK11,sK10))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11))
    | spl179_40 ),
    inference(resolution,[],[f4235,f3200])).

fof(f3200,plain,(
    ! [X0,X1] :
      ( sQ178_eqProxy(X0,X1)
      | r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1836,f3108])).

fof(f1836,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK18(X0,X1),sK19(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1318])).

fof(f7136,plain,(
    spl179_38 ),
    inference(avatar_contradiction_clause,[],[f7135])).

fof(f7135,plain,
    ( $false
    | spl179_38 ),
    inference(subsumption_resolution,[],[f7134,f1738])).

fof(f1738,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f655])).

fof(f655,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f7134,plain,
    ( ~ v1_relat_1(k6_relat_1(sK10))
    | spl179_38 ),
    inference(subsumption_resolution,[],[f7128,f1720])).

fof(f7128,plain,
    ( ~ v1_relat_1(sK11)
    | ~ v1_relat_1(k6_relat_1(sK10))
    | spl179_38 ),
    inference(resolution,[],[f4227,f2197])).

fof(f2197,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1046])).

fof(f1046,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1045])).

fof(f1045,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f654])).

fof(f654,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f4227,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK10),sK11))
    | spl179_38 ),
    inference(avatar_component_clause,[],[f4225])).
%------------------------------------------------------------------------------
