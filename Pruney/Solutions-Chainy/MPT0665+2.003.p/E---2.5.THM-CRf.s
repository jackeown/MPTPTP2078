%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 126 expanded)
%              Number of clauses        :   26 (  49 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  205 ( 586 expanded)
%              Number of equality atoms :   36 (  51 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t73_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X1,X2) )
       => r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(c_0_7,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X9,X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(X9,X10),X6)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(k4_tarski(X11,X12),X6)
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | ~ r2_hidden(esk1_3(X6,X7,X8),X7)
        | ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | v1_relat_1(k7_relat_1(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X1,k1_relat_1(X3))
            & r2_hidden(X1,X2) )
         => r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t73_funct_1])).

fof(c_0_10,plain,(
    ! [X40,X41,X42] :
      ( ( r2_hidden(X40,k1_relat_1(X42))
        | ~ r2_hidden(k4_tarski(X40,X41),X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( X41 = k1_funct_1(X42,X40)
        | ~ r2_hidden(k4_tarski(X40,X41),X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( ~ r2_hidden(X40,k1_relat_1(X42))
        | X41 != k1_funct_1(X42,X40)
        | r2_hidden(k4_tarski(X40,X41),X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X1,X3),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X5 != k7_relat_1(X4,X2)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & v1_funct_1(esk11_0)
    & r2_hidden(esk9_0,k1_relat_1(esk11_0))
    & r2_hidden(esk9_0,esk10_0)
    & ~ r2_hidden(k1_funct_1(esk11_0,esk9_0),k2_relat_1(k7_relat_1(esk11_0,esk10_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk9_0,k1_relat_1(esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,X1),k7_relat_1(X2,esk10_0))
    | ~ r2_hidden(k4_tarski(esk9_0,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,k1_funct_1(esk11_0,esk9_0)),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

fof(c_0_23,plain,(
    ! [X28,X29,X30,X32,X33,X34,X36] :
      ( ( r2_hidden(esk6_3(X28,X29,X30),k1_relat_1(X28))
        | ~ r2_hidden(X30,X29)
        | X29 != k2_relat_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( X30 = k1_funct_1(X28,esk6_3(X28,X29,X30))
        | ~ r2_hidden(X30,X29)
        | X29 != k2_relat_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( ~ r2_hidden(X33,k1_relat_1(X28))
        | X32 != k1_funct_1(X28,X33)
        | r2_hidden(X32,X29)
        | X29 != k2_relat_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( ~ r2_hidden(esk7_2(X28,X34),X34)
        | ~ r2_hidden(X36,k1_relat_1(X28))
        | esk7_2(X28,X34) != k1_funct_1(X28,X36)
        | X34 = k2_relat_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( r2_hidden(esk8_2(X28,X34),k1_relat_1(X28))
        | r2_hidden(esk7_2(X28,X34),X34)
        | X34 = k2_relat_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( esk7_2(X28,X34) = k1_funct_1(X28,esk8_2(X28,X34))
        | r2_hidden(esk7_2(X28,X34),X34)
        | X34 = k2_relat_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_24,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(X17,esk3_3(X15,X16,X17)),X15)
        | X16 != k1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X19,X20),X15)
        | r2_hidden(X19,X16)
        | X16 != k1_relat_1(X15) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(esk4_2(X21,X22),X24),X21)
        | X22 = k1_relat_1(X21) )
      & ( r2_hidden(esk4_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk4_2(X21,X22),esk5_2(X21,X22)),X21)
        | X22 = k1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_25,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,k1_funct_1(esk11_0,esk9_0)),k7_relat_1(esk11_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_20])])).

fof(c_0_27,plain,(
    ! [X38,X39] :
      ( ( v1_relat_1(k7_relat_1(X38,X39))
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( v1_funct_1(k7_relat_1(X38,X39))
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk11_0,esk10_0),esk9_0) = k1_funct_1(esk11_0,esk9_0)
    | ~ v1_funct_1(k7_relat_1(esk11_0,esk10_0))
    | ~ v1_relat_1(k7_relat_1(esk11_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk11_0,esk10_0),esk9_0) = k1_funct_1(esk11_0,esk9_0)
    | ~ v1_relat_1(k7_relat_1(esk11_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_19]),c_0_20])])).

cnf(c_0_35,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk11_0,esk10_0),esk9_0) = k1_funct_1(esk11_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_12]),c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk11_0,esk9_0),k2_relat_1(k7_relat_1(esk11_0,esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk11_0,esk10_0))
    | ~ v1_relat_1(k7_relat_1(esk11_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_26]),c_0_36]),c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk11_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_19]),c_0_20])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_12]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:25:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.20/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(d11_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(v1_relat_1(X3)=>(X3=k7_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X4,X2)&r2_hidden(k4_tarski(X4,X5),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 0.20/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.38  fof(t73_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X1,X2))=>r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 0.20/0.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.20/0.38  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.38  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.38  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.20/0.38  fof(c_0_7, plain, ![X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X9,X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&(r2_hidden(k4_tarski(X9,X10),X6)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6)))&(~r2_hidden(X11,X7)|~r2_hidden(k4_tarski(X11,X12),X6)|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6)))&((~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|(~r2_hidden(esk1_3(X6,X7,X8),X7)|~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6))|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&((r2_hidden(esk1_3(X6,X7,X8),X7)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&(r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).
% 0.20/0.38  fof(c_0_8, plain, ![X26, X27]:(~v1_relat_1(X26)|v1_relat_1(k7_relat_1(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X1,X2))=>r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2)))))), inference(assume_negation,[status(cth)],[t73_funct_1])).
% 0.20/0.38  fof(c_0_10, plain, ![X40, X41, X42]:(((r2_hidden(X40,k1_relat_1(X42))|~r2_hidden(k4_tarski(X40,X41),X42)|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(X41=k1_funct_1(X42,X40)|~r2_hidden(k4_tarski(X40,X41),X42)|(~v1_relat_1(X42)|~v1_funct_1(X42))))&(~r2_hidden(X40,k1_relat_1(X42))|X41!=k1_funct_1(X42,X40)|r2_hidden(k4_tarski(X40,X41),X42)|(~v1_relat_1(X42)|~v1_funct_1(X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.20/0.38  cnf(c_0_11, plain, (r2_hidden(k4_tarski(X1,X3),X5)|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X5!=k7_relat_1(X4,X2)|~v1_relat_1(X5)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_12, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk11_0)&v1_funct_1(esk11_0))&((r2_hidden(esk9_0,k1_relat_1(esk11_0))&r2_hidden(esk9_0,esk10_0))&~r2_hidden(k1_funct_1(esk11_0,esk9_0),k2_relat_1(k7_relat_1(esk11_0,esk10_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.38  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]), c_0_12])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (r2_hidden(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(esk9_0,k1_relat_1(esk11_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,X1),k7_relat_1(X2,esk10_0))|~r2_hidden(k4_tarski(esk9_0,X1),X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,k1_funct_1(esk11_0,esk9_0)),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.38  fof(c_0_23, plain, ![X28, X29, X30, X32, X33, X34, X36]:((((r2_hidden(esk6_3(X28,X29,X30),k1_relat_1(X28))|~r2_hidden(X30,X29)|X29!=k2_relat_1(X28)|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(X30=k1_funct_1(X28,esk6_3(X28,X29,X30))|~r2_hidden(X30,X29)|X29!=k2_relat_1(X28)|(~v1_relat_1(X28)|~v1_funct_1(X28))))&(~r2_hidden(X33,k1_relat_1(X28))|X32!=k1_funct_1(X28,X33)|r2_hidden(X32,X29)|X29!=k2_relat_1(X28)|(~v1_relat_1(X28)|~v1_funct_1(X28))))&((~r2_hidden(esk7_2(X28,X34),X34)|(~r2_hidden(X36,k1_relat_1(X28))|esk7_2(X28,X34)!=k1_funct_1(X28,X36))|X34=k2_relat_1(X28)|(~v1_relat_1(X28)|~v1_funct_1(X28)))&((r2_hidden(esk8_2(X28,X34),k1_relat_1(X28))|r2_hidden(esk7_2(X28,X34),X34)|X34=k2_relat_1(X28)|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(esk7_2(X28,X34)=k1_funct_1(X28,esk8_2(X28,X34))|r2_hidden(esk7_2(X28,X34),X34)|X34=k2_relat_1(X28)|(~v1_relat_1(X28)|~v1_funct_1(X28)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.38  fof(c_0_24, plain, ![X15, X16, X17, X19, X20, X21, X22, X24]:(((~r2_hidden(X17,X16)|r2_hidden(k4_tarski(X17,esk3_3(X15,X16,X17)),X15)|X16!=k1_relat_1(X15))&(~r2_hidden(k4_tarski(X19,X20),X15)|r2_hidden(X19,X16)|X16!=k1_relat_1(X15)))&((~r2_hidden(esk4_2(X21,X22),X22)|~r2_hidden(k4_tarski(esk4_2(X21,X22),X24),X21)|X22=k1_relat_1(X21))&(r2_hidden(esk4_2(X21,X22),X22)|r2_hidden(k4_tarski(esk4_2(X21,X22),esk5_2(X21,X22)),X21)|X22=k1_relat_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.38  cnf(c_0_25, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,k1_funct_1(esk11_0,esk9_0)),k7_relat_1(esk11_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_20])])).
% 0.20/0.38  fof(c_0_27, plain, ![X38, X39]:((v1_relat_1(k7_relat_1(X38,X39))|(~v1_relat_1(X38)|~v1_funct_1(X38)))&(v1_funct_1(k7_relat_1(X38,X39))|(~v1_relat_1(X38)|~v1_funct_1(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.20/0.38  cnf(c_0_28, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_29, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (k1_funct_1(k7_relat_1(esk11_0,esk10_0),esk9_0)=k1_funct_1(esk11_0,esk9_0)|~v1_funct_1(k7_relat_1(esk11_0,esk10_0))|~v1_relat_1(k7_relat_1(esk11_0,esk10_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.38  cnf(c_0_31, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_32, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).
% 0.20/0.38  cnf(c_0_33, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (k1_funct_1(k7_relat_1(esk11_0,esk10_0),esk9_0)=k1_funct_1(esk11_0,esk9_0)|~v1_relat_1(k7_relat_1(esk11_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_19]), c_0_20])])).
% 0.20/0.38  cnf(c_0_35, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (k1_funct_1(k7_relat_1(esk11_0,esk10_0),esk9_0)=k1_funct_1(esk11_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_12]), c_0_20])])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (~r2_hidden(k1_funct_1(esk11_0,esk9_0),k2_relat_1(k7_relat_1(esk11_0,esk10_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (~v1_funct_1(k7_relat_1(esk11_0,esk10_0))|~v1_relat_1(k7_relat_1(esk11_0,esk10_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_26]), c_0_36]), c_0_37])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (~v1_relat_1(k7_relat_1(esk11_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_31]), c_0_19]), c_0_20])])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_12]), c_0_20])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 41
% 0.20/0.38  # Proof object clause steps            : 26
% 0.20/0.38  # Proof object formula steps           : 15
% 0.20/0.38  # Proof object conjectures             : 17
% 0.20/0.38  # Proof object clause conjectures      : 14
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 12
% 0.20/0.38  # Proof object initial formulas used   : 7
% 0.20/0.38  # Proof object generating inferences   : 10
% 0.20/0.38  # Proof object simplifying inferences  : 23
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 7
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 27
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 27
% 0.20/0.38  # Processed clauses                    : 93
% 0.20/0.38  # ...of these trivial                  : 3
% 0.20/0.38  # ...subsumed                          : 6
% 0.20/0.38  # ...remaining for further processing  : 84
% 0.20/0.38  # Other redundant clauses eliminated   : 10
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 1
% 0.20/0.38  # Generated clauses                    : 133
% 0.20/0.38  # ...of the previous two non-trivial   : 119
% 0.20/0.38  # Contextual simplify-reflections      : 3
% 0.20/0.38  # Paramodulations                      : 124
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 10
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 47
% 0.20/0.38  #    Positive orientable unit clauses  : 14
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 31
% 0.20/0.38  # Current number of unprocessed clauses: 78
% 0.20/0.38  # ...number of literals in the above   : 311
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 28
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 580
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 119
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 11
% 0.20/0.38  # Unit Clause-clause subsumption calls : 12
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 2
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 5186
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
