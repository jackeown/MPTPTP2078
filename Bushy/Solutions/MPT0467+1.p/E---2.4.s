%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t55_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:03 EDT 2019

% Result     : Theorem 264.48s
% Output     : CNFRefutation 264.48s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 315 expanded)
%              Number of clauses        :   38 ( 143 expanded)
%              Number of leaves         :    3 (  84 expanded)
%              Depth                    :   23
%              Number of atoms          :  294 (2673 expanded)
%              Number of equality atoms :   45 ( 348 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t55_relat_1.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t55_relat_1.p',dt_k5_relat_1)).

fof(t55_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t55_relat_1.p',t55_relat_1)).

fof(c_0_3,plain,(
    ! [X20,X21,X22,X23,X24,X26,X27,X28,X31] :
      ( ( r2_hidden(k4_tarski(X23,esk6_5(X20,X21,X22,X23,X24)),X20)
        | ~ r2_hidden(k4_tarski(X23,X24),X22)
        | X22 != k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk6_5(X20,X21,X22,X23,X24),X24),X21)
        | ~ r2_hidden(k4_tarski(X23,X24),X22)
        | X22 != k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X26,X28),X20)
        | ~ r2_hidden(k4_tarski(X28,X27),X21)
        | r2_hidden(k4_tarski(X26,X27),X22)
        | X22 != k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk7_3(X20,X21,X22),esk8_3(X20,X21,X22)),X22)
        | ~ r2_hidden(k4_tarski(esk7_3(X20,X21,X22),X31),X20)
        | ~ r2_hidden(k4_tarski(X31,esk8_3(X20,X21,X22)),X21)
        | X22 = k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk7_3(X20,X21,X22),esk9_3(X20,X21,X22)),X20)
        | r2_hidden(k4_tarski(esk7_3(X20,X21,X22),esk8_3(X20,X21,X22)),X22)
        | X22 = k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk9_3(X20,X21,X22),esk8_3(X20,X21,X22)),X21)
        | r2_hidden(k4_tarski(esk7_3(X20,X21,X22),esk8_3(X20,X21,X22)),X22)
        | X22 = k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_4,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ v1_relat_1(X34)
      | v1_relat_1(k5_relat_1(X33,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_5,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_5]),c_0_6])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(esk9_3(X1,X2,X3),esk8_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk7_3(X1,X2,X3),esk8_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,plain,
    ( X1 = k5_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk8_3(X2,X3,X1)),X1)
    | r2_hidden(k4_tarski(X4,esk8_3(X2,X3,X1)),k5_relat_1(X5,X3))
    | ~ r2_hidden(k4_tarski(X4,esk9_3(X2,X3,X1)),X5)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk6_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,plain,
    ( X1 = k5_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk6_5(X4,X5,X6,X7,esk9_3(X2,X3,X1)),esk8_3(X2,X3,X1)),k5_relat_1(X5,X3))
    | r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk8_3(X2,X3,X1)),X1)
    | X6 != k5_relat_1(X4,X5)
    | ~ r2_hidden(k4_tarski(X7,esk9_3(X2,X3,X1)),X6)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,plain,
    ( X3 = k5_relat_1(X1,X2)
    | ~ r2_hidden(k4_tarski(esk7_3(X1,X2,X3),esk8_3(X1,X2,X3)),X3)
    | ~ r2_hidden(k4_tarski(esk7_3(X1,X2,X3),X4),X1)
    | ~ r2_hidden(k4_tarski(X4,esk8_3(X1,X2,X3)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_13,plain,
    ( X1 = k5_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk6_5(X4,X5,k5_relat_1(X4,X5),X6,esk9_3(X2,X3,X1)),esk8_3(X2,X3,X1)),k5_relat_1(X5,X3))
    | r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk8_3(X2,X3,X1)),X1)
    | ~ r2_hidden(k4_tarski(X6,esk9_3(X2,X3,X1)),k5_relat_1(X4,X5))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_6])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,X2,X3),esk9_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk7_3(X1,X2,X3),esk8_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_15,plain,
    ( X1 = k5_relat_1(X2,X3)
    | X4 != k5_relat_1(X5,X3)
    | ~ r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk6_5(X5,X3,X4,X6,esk8_3(X2,X3,X1))),X2)
    | ~ r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk8_3(X2,X3,X1)),X1)
    | ~ r2_hidden(k4_tarski(X6,esk8_3(X2,X3,X1)),X4)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_16,plain,
    ( X1 = k5_relat_1(k5_relat_1(X2,X3),X4)
    | r2_hidden(k4_tarski(esk6_5(X2,X3,k5_relat_1(X2,X3),esk7_3(k5_relat_1(X2,X3),X4,X1),esk9_3(k5_relat_1(X2,X3),X4,X1)),esk8_3(k5_relat_1(X2,X3),X4,X1)),k5_relat_1(X3,X4))
    | r2_hidden(k4_tarski(esk7_3(k5_relat_1(X2,X3),X4,X1),esk8_3(k5_relat_1(X2,X3),X4,X1)),X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_6])).

cnf(c_0_17,plain,
    ( X1 = k5_relat_1(X2,X3)
    | ~ r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk6_5(X4,X3,k5_relat_1(X4,X3),X5,esk8_3(X2,X3,X1))),X2)
    | ~ r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk8_3(X2,X3,X1)),X1)
    | ~ r2_hidden(k4_tarski(X5,esk8_3(X2,X3,X1)),k5_relat_1(X4,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_6])).

cnf(c_0_18,plain,
    ( X1 = k5_relat_1(k5_relat_1(X2,X3),X4)
    | r2_hidden(k4_tarski(esk7_3(k5_relat_1(X2,X3),X4,X1),esk8_3(k5_relat_1(X2,X3),X4,X1)),X1)
    | r2_hidden(k4_tarski(X5,esk8_3(k5_relat_1(X2,X3),X4,X1)),k5_relat_1(X6,k5_relat_1(X3,X4)))
    | ~ r2_hidden(k4_tarski(X5,esk6_5(X2,X3,k5_relat_1(X2,X3),esk7_3(k5_relat_1(X2,X3),X4,X1),esk9_3(k5_relat_1(X2,X3),X4,X1))),X6)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_16]),c_0_6])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,esk6_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_20,plain,
    ( X1 = k5_relat_1(X2,X3)
    | X4 != k5_relat_1(X5,k5_relat_1(X6,X3))
    | ~ r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk6_5(X6,X3,k5_relat_1(X6,X3),esk6_5(X5,k5_relat_1(X6,X3),X4,X7,esk8_3(X2,X3,X1)),esk8_3(X2,X3,X1))),X2)
    | ~ r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk8_3(X2,X3,X1)),X1)
    | ~ r2_hidden(k4_tarski(X7,esk8_3(X2,X3,X1)),X4)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_10]),c_0_6])).

cnf(c_0_21,plain,
    ( X1 = k5_relat_1(k5_relat_1(X2,X3),X4)
    | r2_hidden(k4_tarski(esk7_3(k5_relat_1(X2,X3),X4,X1),esk8_3(k5_relat_1(X2,X3),X4,X1)),k5_relat_1(X2,k5_relat_1(X3,X4)))
    | r2_hidden(k4_tarski(esk7_3(k5_relat_1(X2,X3),X4,X1),esk8_3(k5_relat_1(X2,X3),X4,X1)),X1)
    | ~ r2_hidden(k4_tarski(esk7_3(k5_relat_1(X2,X3),X4,X1),esk9_3(k5_relat_1(X2,X3),X4,X1)),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_6])).

cnf(c_0_22,plain,
    ( X1 = k5_relat_1(X2,X3)
    | ~ r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk6_5(X4,X3,k5_relat_1(X4,X3),esk6_5(X5,k5_relat_1(X4,X3),k5_relat_1(X5,k5_relat_1(X4,X3)),X6,esk8_3(X2,X3,X1)),esk8_3(X2,X3,X1))),X2)
    | ~ r2_hidden(k4_tarski(X6,esk8_3(X2,X3,X1)),k5_relat_1(X5,k5_relat_1(X4,X3)))
    | ~ r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk8_3(X2,X3,X1)),X1)
    | ~ v1_relat_1(k5_relat_1(X5,k5_relat_1(X4,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( X1 = k5_relat_1(k5_relat_1(X2,X3),X4)
    | r2_hidden(k4_tarski(esk7_3(k5_relat_1(X2,X3),X4,X1),esk8_3(k5_relat_1(X2,X3),X4,X1)),k5_relat_1(X2,k5_relat_1(X3,X4)))
    | r2_hidden(k4_tarski(esk7_3(k5_relat_1(X2,X3),X4,X1),esk8_3(k5_relat_1(X2,X3),X4,X1)),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_6])).

cnf(c_0_24,plain,
    ( X1 = k5_relat_1(X2,X3)
    | ~ r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk6_5(X4,X3,k5_relat_1(X4,X3),esk6_5(X5,k5_relat_1(X4,X3),k5_relat_1(X5,k5_relat_1(X4,X3)),X6,esk8_3(X2,X3,X1)),esk8_3(X2,X3,X1))),X2)
    | ~ r2_hidden(k4_tarski(X6,esk8_3(X2,X3,X1)),k5_relat_1(X5,k5_relat_1(X4,X3)))
    | ~ r2_hidden(k4_tarski(esk7_3(X2,X3,X1),esk8_3(X2,X3,X1)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_6]),c_0_6])).

cnf(c_0_25,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(esk7_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),k5_relat_1(X1,k5_relat_1(X2,X3)))
    | ~ v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(ef,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(esk7_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))),esk6_5(X4,X3,k5_relat_1(X4,X3),esk6_5(X5,k5_relat_1(X4,X3),k5_relat_1(X5,k5_relat_1(X4,X3)),X6,esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))))),k5_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X6,esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),k5_relat_1(X5,k5_relat_1(X4,X3)))
    | ~ v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_6])).

cnf(c_0_27,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(esk7_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))),esk6_5(X4,X3,k5_relat_1(X4,X3),esk6_5(X5,k5_relat_1(X4,X3),k5_relat_1(X5,k5_relat_1(X4,X3)),X6,esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))))),k5_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X6,esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),k5_relat_1(X5,k5_relat_1(X4,X3)))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_6]),c_0_6])).

cnf(c_0_28,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(esk7_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))),esk6_5(X2,X3,k5_relat_1(X2,X3),esk6_5(X1,k5_relat_1(X2,X3),k5_relat_1(X1,k5_relat_1(X2,X3)),esk7_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_29,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(esk7_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))),esk6_5(X2,X3,k5_relat_1(X2,X3),esk6_5(X1,k5_relat_1(X2,X3),k5_relat_1(X1,k5_relat_1(X2,X3)),esk7_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_6]),c_0_6])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,esk6_5(X2,X3,X4,X5,X6)),k5_relat_1(X7,X2))
    | X4 != k5_relat_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X1,X5),X7)
    | ~ r2_hidden(k4_tarski(X5,X6),X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X7)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_7,c_0_19])).

cnf(c_0_31,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(esk6_5(X1,k5_relat_1(X2,X3),k5_relat_1(X1,k5_relat_1(X2,X3)),esk7_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),k5_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(esk7_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))),esk6_5(X1,k5_relat_1(X2,X3),k5_relat_1(X1,k5_relat_1(X2,X3)),esk7_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))))),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_6])).

cnf(c_0_32,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(esk6_5(X1,k5_relat_1(X2,X3),k5_relat_1(X1,k5_relat_1(X2,X3)),esk7_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),k5_relat_1(X2,X3))
    | ~ v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_19]),c_0_6]),c_0_25])).

cnf(c_0_33,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(esk6_5(X1,k5_relat_1(X2,X3),k5_relat_1(X1,k5_relat_1(X2,X3)),esk7_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),esk8_3(k5_relat_1(X1,X2),X3,k5_relat_1(X1,k5_relat_1(X2,X3)))),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_6]),c_0_6])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t55_relat_1])).

cnf(c_0_35,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_10]),c_0_6]),c_0_25])).

fof(c_0_36,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & k5_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0) != k5_relat_1(esk1_0,k5_relat_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

cnf(c_0_37,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_6]),c_0_6])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk1_0,X1),X2) = k5_relat_1(esk1_0,k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk1_0,esk2_0),X1) = k5_relat_1(esk1_0,k5_relat_1(esk2_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0) != k5_relat_1(esk1_0,k5_relat_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
