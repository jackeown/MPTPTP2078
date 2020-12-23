%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0766+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:52 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   18 (  42 expanded)
%              Number of clauses        :   11 (  14 expanded)
%              Number of leaves         :    3 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :  103 ( 379 expanded)
%              Number of equality atoms :    3 (  24 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & ? [X3] :
                  ( r2_hidden(X3,k3_relat_1(X1))
                  & ~ r2_hidden(k4_tarski(X3,X2),X1) )
              & ! [X3] :
                  ~ ( r2_hidden(X3,k3_relat_1(X1))
                    & r2_hidden(k4_tarski(X2,X3),X1)
                    & ! [X4] :
                        ~ ( r2_hidden(X4,k3_relat_1(X1))
                          & r2_hidden(k4_tarski(X2,X4),X1)
                          & X4 != X2
                          & ~ r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => ! [X2] :
              ~ ( r2_hidden(X2,k3_relat_1(X1))
                & ? [X3] :
                    ( r2_hidden(X3,k3_relat_1(X1))
                    & ~ r2_hidden(k4_tarski(X3,X2),X1) )
                & ! [X3] :
                    ~ ( r2_hidden(X3,k3_relat_1(X1))
                      & r2_hidden(k4_tarski(X2,X3),X1)
                      & ! [X4] :
                          ~ ( r2_hidden(X4,k3_relat_1(X1))
                            & r2_hidden(k4_tarski(X2,X4),X1)
                            & X4 != X2
                            & ~ r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_wellord1])).

fof(c_0_4,negated_conjecture,(
    ! [X3398] :
      ( v1_relat_1(esk271_0)
      & v2_wellord1(esk271_0)
      & r2_hidden(esk272_0,k3_relat_1(esk271_0))
      & r2_hidden(esk273_0,k3_relat_1(esk271_0))
      & ~ r2_hidden(k4_tarski(esk273_0,esk272_0),esk271_0)
      & ( r2_hidden(esk274_1(X3398),k3_relat_1(esk271_0))
        | ~ r2_hidden(X3398,k3_relat_1(esk271_0))
        | ~ r2_hidden(k4_tarski(esk272_0,X3398),esk271_0) )
      & ( r2_hidden(k4_tarski(esk272_0,esk274_1(X3398)),esk271_0)
        | ~ r2_hidden(X3398,k3_relat_1(esk271_0))
        | ~ r2_hidden(k4_tarski(esk272_0,X3398),esk271_0) )
      & ( esk274_1(X3398) != esk272_0
        | ~ r2_hidden(X3398,k3_relat_1(esk271_0))
        | ~ r2_hidden(k4_tarski(esk272_0,X3398),esk271_0) )
      & ( ~ r2_hidden(k4_tarski(X3398,esk274_1(X3398)),esk271_0)
        | ~ r2_hidden(X3398,k3_relat_1(esk271_0))
        | ~ r2_hidden(k4_tarski(esk272_0,X3398),esk271_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

fof(c_0_5,plain,(
    ! [X3357] :
      ( ( v1_relat_2(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( v8_relat_2(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( v4_relat_2(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( v6_relat_2(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( v1_wellord1(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( ~ v1_relat_2(X3357)
        | ~ v8_relat_2(X3357)
        | ~ v4_relat_2(X3357)
        | ~ v6_relat_2(X3357)
        | ~ v1_wellord1(X3357)
        | v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

cnf(c_0_6,negated_conjecture,
    ( r2_hidden(k4_tarski(esk272_0,esk274_1(X1)),esk271_0)
    | ~ r2_hidden(X1,k3_relat_1(esk271_0))
    | ~ r2_hidden(k4_tarski(esk272_0,X1),esk271_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(esk272_0,k3_relat_1(esk271_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,plain,(
    ! [X3370,X3371] :
      ( ( ~ v1_relat_2(X3370)
        | ~ r2_hidden(X3371,k3_relat_1(X3370))
        | r2_hidden(k4_tarski(X3371,X3371),X3370)
        | ~ v1_relat_1(X3370) )
      & ( r2_hidden(esk263_1(X3370),k3_relat_1(X3370))
        | v1_relat_2(X3370)
        | ~ v1_relat_1(X3370) )
      & ( ~ r2_hidden(k4_tarski(esk263_1(X3370),esk263_1(X3370)),X3370)
        | v1_relat_2(X3370)
        | ~ v1_relat_1(X3370) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_9,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk271_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( v2_wellord1(esk271_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk274_1(X1)),esk271_0)
    | ~ r2_hidden(X1,k3_relat_1(esk271_0))
    | ~ r2_hidden(k4_tarski(esk272_0,X1),esk271_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(k4_tarski(esk272_0,esk274_1(esk272_0)),esk271_0)
    | ~ r2_hidden(k4_tarski(esk272_0,esk272_0),esk271_0) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_2(esk271_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk272_0,esk272_0),esk271_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_7]),c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_7]),c_0_15]),c_0_10])]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
