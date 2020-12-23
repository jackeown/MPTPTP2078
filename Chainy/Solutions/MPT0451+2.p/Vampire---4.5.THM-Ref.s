%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0451+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:31 EST 2020

% Result     : Theorem 4.00s
% Output     : Refutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 215 expanded)
%              Number of leaves         :   20 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  336 ( 931 expanded)
%              Number of equality atoms :   47 ( 168 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5943,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3593,f3834,f3844,f3901,f3916,f5925,f5942])).

fof(f5942,plain,
    ( ~ spl132_5
    | ~ spl132_6 ),
    inference(avatar_contradiction_clause,[],[f5941])).

fof(f5941,plain,
    ( $false
    | ~ spl132_5
    | ~ spl132_6 ),
    inference(subsumption_resolution,[],[f5940,f3833])).

fof(f3833,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK62(sK3,k1_relat_1(k4_relat_1(sK3)))),sK3)
    | ~ spl132_6 ),
    inference(avatar_component_clause,[],[f3832])).

fof(f3832,plain,
    ( spl132_6
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK62(sK3,k1_relat_1(k4_relat_1(sK3)))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl132_6])])).

fof(f5940,plain,
    ( r2_hidden(k4_tarski(sK67(k4_relat_1(sK3),sK62(sK3,k1_relat_1(k4_relat_1(sK3)))),sK62(sK3,k1_relat_1(k4_relat_1(sK3)))),sK3)
    | ~ spl132_5 ),
    inference(subsumption_resolution,[],[f5935,f1529])).

fof(f1529,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f1158])).

fof(f1158,plain,
    ( ( k1_relat_1(sK3) != k2_relat_1(k4_relat_1(sK3))
      | k2_relat_1(sK3) != k1_relat_1(k4_relat_1(sK3)) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f693,f1157])).

fof(f1157,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k4_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(k4_relat_1(X0)) )
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK3) != k2_relat_1(k4_relat_1(sK3))
        | k2_relat_1(sK3) != k1_relat_1(k4_relat_1(sK3)) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f693,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k4_relat_1(X0))
        | k2_relat_1(X0) != k1_relat_1(k4_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f676])).

fof(f676,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f675])).

fof(f675,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f5935,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(k4_tarski(sK67(k4_relat_1(sK3),sK62(sK3,k1_relat_1(k4_relat_1(sK3)))),sK62(sK3,k1_relat_1(k4_relat_1(sK3)))),sK3)
    | ~ spl132_5 ),
    inference(resolution,[],[f3650,f3829])).

fof(f3829,plain,
    ( r2_hidden(sK62(sK3,k1_relat_1(k4_relat_1(sK3))),k1_relat_1(k4_relat_1(sK3)))
    | ~ spl132_5 ),
    inference(avatar_component_clause,[],[f3828])).

fof(f3828,plain,
    ( spl132_5
  <=> r2_hidden(sK62(sK3,k1_relat_1(k4_relat_1(sK3))),k1_relat_1(k4_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl132_5])])).

fof(f3650,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k1_relat_1(k4_relat_1(X5)))
      | ~ v1_relat_1(X5)
      | r2_hidden(k4_tarski(sK67(k4_relat_1(X5),X6),X6),X5) ) ),
    inference(resolution,[],[f3647,f2618])).

fof(f2618,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK67(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f1974])).

fof(f1974,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK67(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1329])).

fof(f1329,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK65(X0,X1),X3),X0)
            | ~ r2_hidden(sK65(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK65(X0,X1),sK66(X0,X1)),X0)
            | r2_hidden(sK65(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK67(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK65,sK66,sK67])],[f1325,f1328,f1327,f1326])).

fof(f1326,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK65(X0,X1),X3),X0)
          | ~ r2_hidden(sK65(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK65(X0,X1),X4),X0)
          | r2_hidden(sK65(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1327,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK65(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK65(X0,X1),sK66(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1328,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK67(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1325,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1324])).

fof(f1324,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f641])).

fof(f641,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f3647,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2597,f1595])).

fof(f1595,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f708])).

fof(f708,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f648])).

fof(f648,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f2597,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1611])).

fof(f1611,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1170])).

fof(f1170,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f1168,f1169])).

fof(f1169,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1168,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1167])).

fof(f1167,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f725])).

fof(f725,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f644])).

fof(f644,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f5925,plain,
    ( ~ spl132_7
    | ~ spl132_8 ),
    inference(avatar_contradiction_clause,[],[f5924])).

fof(f5924,plain,
    ( $false
    | ~ spl132_7
    | ~ spl132_8 ),
    inference(subsumption_resolution,[],[f5923,f3843])).

fof(f3843,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK65(sK3,k2_relat_1(k4_relat_1(sK3))),X0),sK3)
    | ~ spl132_8 ),
    inference(avatar_component_clause,[],[f3842])).

fof(f3842,plain,
    ( spl132_8
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK65(sK3,k2_relat_1(k4_relat_1(sK3))),X0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl132_8])])).

fof(f5923,plain,
    ( r2_hidden(k4_tarski(sK65(sK3,k2_relat_1(k4_relat_1(sK3))),sK64(k4_relat_1(sK3),sK65(sK3,k2_relat_1(k4_relat_1(sK3))))),sK3)
    | ~ spl132_7 ),
    inference(subsumption_resolution,[],[f5918,f1529])).

fof(f5918,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(k4_tarski(sK65(sK3,k2_relat_1(k4_relat_1(sK3))),sK64(k4_relat_1(sK3),sK65(sK3,k2_relat_1(k4_relat_1(sK3))))),sK3)
    | ~ spl132_7 ),
    inference(resolution,[],[f3649,f3839])).

fof(f3839,plain,
    ( r2_hidden(sK65(sK3,k2_relat_1(k4_relat_1(sK3))),k2_relat_1(k4_relat_1(sK3)))
    | ~ spl132_7 ),
    inference(avatar_component_clause,[],[f3838])).

fof(f3838,plain,
    ( spl132_7
  <=> r2_hidden(sK65(sK3,k2_relat_1(k4_relat_1(sK3))),k2_relat_1(k4_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl132_7])])).

fof(f3649,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k2_relat_1(k4_relat_1(X4)))
      | ~ v1_relat_1(X4)
      | r2_hidden(k4_tarski(X3,sK64(k4_relat_1(X4),X3)),X4) ) ),
    inference(resolution,[],[f3647,f2616])).

fof(f2616,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK64(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f1970])).

fof(f1970,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK64(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1323])).

fof(f1323,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK62(X0,X1)),X0)
            | ~ r2_hidden(sK62(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK63(X0,X1),sK62(X0,X1)),X0)
            | r2_hidden(sK62(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK64(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK62,sK63,sK64])],[f1319,f1322,f1321,f1320])).

fof(f1320,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK62(X0,X1)),X0)
          | ~ r2_hidden(sK62(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK62(X0,X1)),X0)
          | r2_hidden(sK62(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1321,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK62(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK63(X0,X1),sK62(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1322,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK64(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1319,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1318])).

fof(f1318,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f642])).

fof(f642,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f3916,plain,
    ( spl132_2
    | spl132_7 ),
    inference(avatar_contradiction_clause,[],[f3914])).

fof(f3914,plain,
    ( $false
    | spl132_2
    | spl132_7 ),
    inference(unit_resulting_resolution,[],[f3592,f3840,f3913,f3030])).

fof(f3030,plain,(
    ! [X0,X1] :
      ( sQ131_eqProxy(k1_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK65(X0,X1),sK66(X0,X1)),X0)
      | r2_hidden(sK65(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f1976,f2787])).

fof(f2787,plain,(
    ! [X1,X0] :
      ( sQ131_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ131_eqProxy])])).

fof(f1976,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK65(X0,X1),sK66(X0,X1)),X0)
      | r2_hidden(sK65(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1329])).

fof(f3913,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK65(sK3,k2_relat_1(k4_relat_1(sK3))),X0),sK3)
    | spl132_7 ),
    inference(subsumption_resolution,[],[f3911,f1529])).

fof(f3911,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK65(sK3,k2_relat_1(k4_relat_1(sK3))),X0),sK3)
        | ~ v1_relat_1(sK3) )
    | spl132_7 ),
    inference(resolution,[],[f3854,f3644])).

fof(f3644,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2596,f1595])).

fof(f2596,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1612])).

fof(f1612,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1170])).

fof(f3854,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK65(sK3,k2_relat_1(k4_relat_1(sK3)))),k4_relat_1(sK3))
    | spl132_7 ),
    inference(resolution,[],[f3840,f2615])).

fof(f2615,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f1971])).

fof(f1971,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1323])).

fof(f3840,plain,
    ( ~ r2_hidden(sK65(sK3,k2_relat_1(k4_relat_1(sK3))),k2_relat_1(k4_relat_1(sK3)))
    | spl132_7 ),
    inference(avatar_component_clause,[],[f3838])).

fof(f3592,plain,
    ( ~ sQ131_eqProxy(k1_relat_1(sK3),k2_relat_1(k4_relat_1(sK3)))
    | spl132_2 ),
    inference(avatar_component_clause,[],[f3590])).

fof(f3590,plain,
    ( spl132_2
  <=> sQ131_eqProxy(k1_relat_1(sK3),k2_relat_1(k4_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl132_2])])).

fof(f3901,plain,
    ( spl132_1
    | spl132_5 ),
    inference(avatar_contradiction_clause,[],[f3899])).

fof(f3899,plain,
    ( $false
    | spl132_1
    | spl132_5 ),
    inference(unit_resulting_resolution,[],[f3588,f3830,f3895,f3028])).

fof(f3028,plain,(
    ! [X0,X1] :
      ( sQ131_eqProxy(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK63(X0,X1),sK62(X0,X1)),X0)
      | r2_hidden(sK62(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f1972,f2787])).

fof(f1972,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK63(X0,X1),sK62(X0,X1)),X0)
      | r2_hidden(sK62(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1323])).

fof(f3895,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK62(sK3,k1_relat_1(k4_relat_1(sK3)))),sK3)
    | spl132_5 ),
    inference(subsumption_resolution,[],[f3893,f1529])).

fof(f3893,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK62(sK3,k1_relat_1(k4_relat_1(sK3)))),sK3)
        | ~ v1_relat_1(sK3) )
    | spl132_5 ),
    inference(resolution,[],[f3836,f3644])).

fof(f3836,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK62(sK3,k1_relat_1(k4_relat_1(sK3))),X0),k4_relat_1(sK3))
    | spl132_5 ),
    inference(resolution,[],[f3830,f2617])).

fof(f2617,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f1975])).

fof(f1975,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1329])).

fof(f3830,plain,
    ( ~ r2_hidden(sK62(sK3,k1_relat_1(k4_relat_1(sK3))),k1_relat_1(k4_relat_1(sK3)))
    | spl132_5 ),
    inference(avatar_component_clause,[],[f3828])).

fof(f3588,plain,
    ( ~ sQ131_eqProxy(k2_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)))
    | spl132_1 ),
    inference(avatar_component_clause,[],[f3586])).

fof(f3586,plain,
    ( spl132_1
  <=> sQ131_eqProxy(k2_relat_1(sK3),k1_relat_1(k4_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl132_1])])).

fof(f3844,plain,
    ( ~ spl132_7
    | spl132_8
    | spl132_2 ),
    inference(avatar_split_clause,[],[f3653,f3590,f3842,f3838])).

fof(f3653,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK65(sK3,k2_relat_1(k4_relat_1(sK3))),X0),sK3)
        | ~ r2_hidden(sK65(sK3,k2_relat_1(k4_relat_1(sK3))),k2_relat_1(k4_relat_1(sK3))) )
    | spl132_2 ),
    inference(resolution,[],[f3029,f3592])).

fof(f3029,plain,(
    ! [X0,X3,X1] :
      ( sQ131_eqProxy(k1_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(sK65(X0,X1),X3),X0)
      | ~ r2_hidden(sK65(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f1977,f2787])).

fof(f1977,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK65(X0,X1),X3),X0)
      | ~ r2_hidden(sK65(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1329])).

fof(f3834,plain,
    ( ~ spl132_5
    | spl132_6
    | spl132_1 ),
    inference(avatar_split_clause,[],[f3652,f3586,f3832,f3828])).

fof(f3652,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK62(sK3,k1_relat_1(k4_relat_1(sK3)))),sK3)
        | ~ r2_hidden(sK62(sK3,k1_relat_1(k4_relat_1(sK3))),k1_relat_1(k4_relat_1(sK3))) )
    | spl132_1 ),
    inference(resolution,[],[f3027,f3588])).

fof(f3027,plain,(
    ! [X0,X3,X1] :
      ( sQ131_eqProxy(k2_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(X3,sK62(X0,X1)),X0)
      | ~ r2_hidden(sK62(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f1973,f2787])).

fof(f1973,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK62(X0,X1)),X0)
      | ~ r2_hidden(sK62(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1323])).

fof(f3593,plain,
    ( ~ spl132_1
    | ~ spl132_2 ),
    inference(avatar_split_clause,[],[f2805,f3590,f3586])).

fof(f2805,plain,
    ( ~ sQ131_eqProxy(k1_relat_1(sK3),k2_relat_1(k4_relat_1(sK3)))
    | ~ sQ131_eqProxy(k2_relat_1(sK3),k1_relat_1(k4_relat_1(sK3))) ),
    inference(equality_proxy_replacement,[],[f1530,f2787,f2787])).

fof(f1530,plain,
    ( k1_relat_1(sK3) != k2_relat_1(k4_relat_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k4_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f1158])).
%------------------------------------------------------------------------------
