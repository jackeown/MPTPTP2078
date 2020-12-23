%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t88_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:05 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   20 (  31 expanded)
%              Number of clauses        :   11 (  13 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 123 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t88_relat_1.p',d3_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t88_relat_1.p',dt_k7_relat_1)).

fof(d11_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( v1_relat_1(X3)
         => ( X3 = k7_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X4,X2)
                  & r2_hidden(k4_tarski(X4,X5),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t88_relat_1.p',d11_relat_1)).

fof(t88_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t88_relat_1.p',t88_relat_1)).

fof(c_0_4,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r1_tarski(X19,X20)
        | ~ r2_hidden(k4_tarski(X21,X22),X19)
        | r2_hidden(k4_tarski(X21,X22),X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk5_2(X19,X23),esk6_2(X19,X23)),X19)
        | r1_tarski(X19,X23)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X19,X23),esk6_2(X19,X23)),X23)
        | r1_tarski(X19,X23)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_5,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | v1_relat_1(k7_relat_1(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_6,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X13,X11)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k7_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(X13,X14),X10)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k7_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(k4_tarski(X15,X16),X10)
        | r2_hidden(k4_tarski(X15,X16),X12)
        | X12 != k7_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X12)
        | ~ r2_hidden(esk3_3(X10,X11,X12),X11)
        | ~ r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X10)
        | X12 = k7_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk3_3(X10,X11,X12),X11)
        | r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X12)
        | X12 = k7_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X10)
        | r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X12)
        | X12 = k7_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k7_relat_1(X3,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk5_2(k7_relat_1(X1,X2),X3),esk6_2(k7_relat_1(X1,X2),X3)),k7_relat_1(X1,X2))
    | r1_tarski(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    inference(assume_negation,[status(cth)],[t88_relat_1])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(esk5_2(k7_relat_1(X1,X2),X3),esk6_2(k7_relat_1(X1,X2),X3)),X4)
    | r1_tarski(k7_relat_1(X1,X2),X3)
    | k7_relat_1(X1,X2) != k7_relat_1(X4,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_8])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ~ r1_tarski(k7_relat_1(esk2_0,esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk5_2(k7_relat_1(X1,X2),X3),esk6_2(k7_relat_1(X1,X2),X3)),X1)
    | r1_tarski(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(esk2_0,esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
