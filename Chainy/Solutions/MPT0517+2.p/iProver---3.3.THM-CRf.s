%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0517+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:43 EST 2020

% Result     : Theorem 23.41s
% Output     : CNFRefutation 23.41s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 ( 228 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f642,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1205,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f642])).

fof(f1728,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1205])).

fof(f1729,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1728])).

fof(f1730,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f1729])).

fof(f1731,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X1)
          | ~ r2_hidden(sK130(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X1)
            & r2_hidden(sK130(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1732,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK130(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X1)
                    & r2_hidden(sK130(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK129(X0,X1,X2),sK130(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK129,sK130])],[f1730,f1731])).

fof(f2809,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1732])).

fof(f3692,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f2809])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1216,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f2847,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1216])).

fof(f645,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1208,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f645])).

fof(f1742,plain,(
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
    inference(nnf_transformation,[],[f1208])).

fof(f1743,plain,(
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
    inference(rectify,[],[f1742])).

fof(f1744,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK136(X0,X1),sK137(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK136(X0,X1),sK137(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1745,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK136(X0,X1),sK137(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK136(X0,X1),sK137(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK136,sK137])],[f1743,f1744])).

fof(f2822,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK136(X0,X1),sK137(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1745])).

fof(f2823,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK136(X0,X1),sK137(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1745])).

fof(f693,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f694,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(negated_conjecture,[],[f693])).

fof(f1259,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k8_relat_1(X0,X1),X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f694])).

fof(f1772,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k8_relat_1(X0,X1),X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k8_relat_1(sK151,sK152),sK152)
      & v1_relat_1(sK152) ) ),
    introduced(choice_axiom,[])).

fof(f1773,plain,
    ( ~ r1_tarski(k8_relat_1(sK151,sK152),sK152)
    & v1_relat_1(sK152) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK151,sK152])],[f1259,f1772])).

fof(f2892,plain,(
    ~ r1_tarski(k8_relat_1(sK151,sK152),sK152) ),
    inference(cnf_transformation,[],[f1773])).

fof(f2891,plain,(
    v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f1773])).

cnf(c_1008,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k8_relat_1(X3,X2)) ),
    inference(cnf_transformation,[],[f3692])).

cnf(c_86280,plain,
    ( ~ r2_hidden(k4_tarski(sK136(k8_relat_1(sK151,sK152),sK152),sK137(k8_relat_1(sK151,sK152),sK152)),k8_relat_1(sK151,sK152))
    | r2_hidden(k4_tarski(sK136(k8_relat_1(sK151,sK152),sK152),sK137(k8_relat_1(sK151,sK152),sK152)),sK152)
    | ~ v1_relat_1(k8_relat_1(sK151,sK152))
    | ~ v1_relat_1(sK152) ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_1043,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f2847])).

cnf(c_65592,plain,
    ( v1_relat_1(k8_relat_1(sK151,sK152))
    | ~ v1_relat_1(sK152) ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_1018,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK136(X0,X1),sK137(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2822])).

cnf(c_58787,plain,
    ( r1_tarski(k8_relat_1(sK151,sK152),sK152)
    | r2_hidden(k4_tarski(sK136(k8_relat_1(sK151,sK152),sK152),sK137(k8_relat_1(sK151,sK152),sK152)),k8_relat_1(sK151,sK152))
    | ~ v1_relat_1(k8_relat_1(sK151,sK152)) ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_1017,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(sK136(X0,X1),sK137(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2823])).

cnf(c_58744,plain,
    ( r1_tarski(k8_relat_1(sK151,sK152),sK152)
    | ~ r2_hidden(k4_tarski(sK136(k8_relat_1(sK151,sK152),sK152),sK137(k8_relat_1(sK151,sK152),sK152)),sK152)
    | ~ v1_relat_1(k8_relat_1(sK151,sK152)) ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_1087,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(sK151,sK152),sK152) ),
    inference(cnf_transformation,[],[f2892])).

cnf(c_1088,negated_conjecture,
    ( v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f2891])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_86280,c_65592,c_58787,c_58744,c_1087,c_1088])).

%------------------------------------------------------------------------------
