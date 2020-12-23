%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0481+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:41 EST 2020

% Result     : Theorem 27.32s
% Output     : CNFRefutation 27.32s
% Verified   : 
% Statistics : Number of formulae       :   51 (  83 expanded)
%              Number of clauses        :   20 (  23 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  175 ( 319 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f718,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1245,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f718])).

fof(f1672,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f1245])).

fof(f1673,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f1672])).

fof(f2802,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1673])).

fof(f719,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1246,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f719])).

fof(f1674,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f1246])).

fof(f1675,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f1674])).

fof(f2805,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1675])).

fof(f654,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2721,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f654])).

fof(f653,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1168,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f653])).

fof(f1169,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1168])).

fof(f2720,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1169])).

fof(f643,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1163,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f643])).

fof(f1635,plain,(
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
    inference(nnf_transformation,[],[f1163])).

fof(f1636,plain,(
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
    inference(rectify,[],[f1635])).

fof(f1637,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK132(X0,X1),sK133(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK132(X0,X1),sK133(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1638,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK132(X0,X1),sK133(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK132(X0,X1),sK133(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK132,sK133])],[f1636,f1637])).

fof(f2699,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK132(X0,X1),sK133(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1638])).

fof(f2698,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK132(X0,X1),sK133(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1638])).

fof(f720,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f721,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f720])).

fof(f1247,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f721])).

fof(f1676,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK152),sK153),sK153)
        | ~ r1_tarski(k5_relat_1(sK153,k6_relat_1(sK152)),sK153) )
      & v1_relat_1(sK153) ) ),
    introduced(choice_axiom,[])).

fof(f1677,plain,
    ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK152),sK153),sK153)
      | ~ r1_tarski(k5_relat_1(sK153,k6_relat_1(sK152)),sK153) )
    & v1_relat_1(sK153) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK152,sK153])],[f1247,f1676])).

fof(f2808,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK152),sK153),sK153)
    | ~ r1_tarski(k5_relat_1(sK153,k6_relat_1(sK152)),sK153) ),
    inference(cnf_transformation,[],[f1677])).

fof(f2807,plain,(
    v1_relat_1(sK153) ),
    inference(cnf_transformation,[],[f1677])).

cnf(c_1110,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2802])).

cnf(c_77411,plain,
    ( ~ r2_hidden(k4_tarski(sK132(k5_relat_1(k6_relat_1(sK152),sK153),sK153),sK133(k5_relat_1(k6_relat_1(sK152),sK153),sK153)),k5_relat_1(k6_relat_1(X0),sK153))
    | r2_hidden(k4_tarski(sK132(k5_relat_1(k6_relat_1(sK152),sK153),sK153),sK133(k5_relat_1(k6_relat_1(sK152),sK153),sK153)),sK153)
    | ~ v1_relat_1(sK153) ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_90124,plain,
    ( ~ r2_hidden(k4_tarski(sK132(k5_relat_1(k6_relat_1(sK152),sK153),sK153),sK133(k5_relat_1(k6_relat_1(sK152),sK153),sK153)),k5_relat_1(k6_relat_1(sK152),sK153))
    | r2_hidden(k4_tarski(sK132(k5_relat_1(k6_relat_1(sK152),sK153),sK153),sK133(k5_relat_1(k6_relat_1(sK152),sK153),sK153)),sK153)
    | ~ v1_relat_1(sK153) ),
    inference(instantiation,[status(thm)],[c_77411])).

cnf(c_1113,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,k6_relat_1(X3)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2805])).

cnf(c_55607,plain,
    ( ~ r2_hidden(k4_tarski(sK132(k5_relat_1(sK153,k6_relat_1(sK152)),sK153),sK133(k5_relat_1(sK153,k6_relat_1(sK152)),sK153)),k5_relat_1(sK153,k6_relat_1(X0)))
    | r2_hidden(k4_tarski(sK132(k5_relat_1(sK153,k6_relat_1(sK152)),sK153),sK133(k5_relat_1(sK153,k6_relat_1(sK152)),sK153)),sK153)
    | ~ v1_relat_1(sK153) ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_83911,plain,
    ( ~ r2_hidden(k4_tarski(sK132(k5_relat_1(sK153,k6_relat_1(sK152)),sK153),sK133(k5_relat_1(sK153,k6_relat_1(sK152)),sK153)),k5_relat_1(sK153,k6_relat_1(sK152)))
    | r2_hidden(k4_tarski(sK132(k5_relat_1(sK153,k6_relat_1(sK152)),sK153),sK133(k5_relat_1(sK153,k6_relat_1(sK152)),sK153)),sK153)
    | ~ v1_relat_1(sK153) ),
    inference(instantiation,[status(thm)],[c_55607])).

cnf(c_1029,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2721])).

cnf(c_58666,plain,
    ( v1_relat_1(k6_relat_1(sK152)) ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_1028,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2720])).

cnf(c_48734,plain,
    ( v1_relat_1(k5_relat_1(sK153,k6_relat_1(sK152)))
    | ~ v1_relat_1(k6_relat_1(sK152))
    | ~ v1_relat_1(sK153) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_48303,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK152),sK153))
    | ~ v1_relat_1(k6_relat_1(sK152))
    | ~ v1_relat_1(sK153) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_1005,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(sK132(X0,X1),sK133(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2699])).

cnf(c_48056,plain,
    ( r1_tarski(k5_relat_1(sK153,k6_relat_1(sK152)),sK153)
    | ~ r2_hidden(k4_tarski(sK132(k5_relat_1(sK153,k6_relat_1(sK152)),sK153),sK133(k5_relat_1(sK153,k6_relat_1(sK152)),sK153)),sK153)
    | ~ v1_relat_1(k5_relat_1(sK153,k6_relat_1(sK152))) ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_1006,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK132(X0,X1),sK133(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2698])).

cnf(c_48060,plain,
    ( r1_tarski(k5_relat_1(sK153,k6_relat_1(sK152)),sK153)
    | r2_hidden(k4_tarski(sK132(k5_relat_1(sK153,k6_relat_1(sK152)),sK153),sK133(k5_relat_1(sK153,k6_relat_1(sK152)),sK153)),k5_relat_1(sK153,k6_relat_1(sK152)))
    | ~ v1_relat_1(k5_relat_1(sK153,k6_relat_1(sK152))) ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_47890,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK152),sK153),sK153)
    | ~ r2_hidden(k4_tarski(sK132(k5_relat_1(k6_relat_1(sK152),sK153),sK153),sK133(k5_relat_1(k6_relat_1(sK152),sK153),sK153)),sK153)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK152),sK153)) ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_47894,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK152),sK153),sK153)
    | r2_hidden(k4_tarski(sK132(k5_relat_1(k6_relat_1(sK152),sK153),sK153),sK133(k5_relat_1(k6_relat_1(sK152),sK153),sK153)),k5_relat_1(k6_relat_1(sK152),sK153))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK152),sK153)) ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_1115,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK152),sK153),sK153)
    | ~ r1_tarski(k5_relat_1(sK153,k6_relat_1(sK152)),sK153) ),
    inference(cnf_transformation,[],[f2808])).

cnf(c_1116,negated_conjecture,
    ( v1_relat_1(sK153) ),
    inference(cnf_transformation,[],[f2807])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_90124,c_83911,c_58666,c_48734,c_48303,c_48056,c_48060,c_47890,c_47894,c_1115,c_1116])).

%------------------------------------------------------------------------------
