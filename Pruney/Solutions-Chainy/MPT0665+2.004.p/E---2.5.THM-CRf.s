%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:15 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   38 (  90 expanded)
%              Number of clauses        :   25 (  35 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  190 ( 417 expanded)
%              Number of equality atoms :   34 (  39 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t73_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X1,X2) )
       => r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

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

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(c_0_6,plain,(
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

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X1,k1_relat_1(X3))
            & r2_hidden(X1,X2) )
         => r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t73_funct_1])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X1,X3),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X5 != k7_relat_1(X4,X2)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & v1_funct_1(esk11_0)
    & r2_hidden(esk9_0,k1_relat_1(esk11_0))
    & r2_hidden(esk9_0,esk10_0)
    & ~ r2_hidden(k1_funct_1(esk11_0,esk9_0),k2_relat_1(k7_relat_1(esk11_0,esk10_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
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

fof(c_0_11,plain,(
    ! [X26,X27,X28,X30,X31,X32,X34] :
      ( ( r2_hidden(esk6_3(X26,X27,X28),k1_relat_1(X26))
        | ~ r2_hidden(X28,X27)
        | X27 != k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( X28 = k1_funct_1(X26,esk6_3(X26,X27,X28))
        | ~ r2_hidden(X28,X27)
        | X27 != k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(X31,k1_relat_1(X26))
        | X30 != k1_funct_1(X26,X31)
        | r2_hidden(X30,X27)
        | X27 != k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(esk7_2(X26,X32),X32)
        | ~ r2_hidden(X34,k1_relat_1(X26))
        | esk7_2(X26,X32) != k1_funct_1(X26,X34)
        | X32 = k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( r2_hidden(esk8_2(X26,X32),k1_relat_1(X26))
        | r2_hidden(esk7_2(X26,X32),X32)
        | X32 = k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( esk7_2(X26,X32) = k1_funct_1(X26,esk8_2(X26,X32))
        | r2_hidden(esk7_2(X26,X32),X32)
        | X32 = k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(k7_relat_1(X3,X4))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X36,X37] :
      ( ( v1_relat_1(k7_relat_1(X36,X37))
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( v1_funct_1(k7_relat_1(X36,X37))
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_16,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X40)
      | ~ v1_funct_1(X40)
      | ~ r2_hidden(X38,X39)
      | k1_funct_1(k7_relat_1(X40,X39),X38) = k1_funct_1(X40,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,X1),k7_relat_1(X2,esk10_0))
    | ~ r2_hidden(k4_tarski(esk9_0,X1),X2)
    | ~ v1_relat_1(k7_relat_1(X2,esk10_0))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk3_3(X1,k1_relat_1(X1),esk9_0)),k7_relat_1(X1,esk10_0))
    | ~ r2_hidden(esk9_0,k1_relat_1(X1))
    | ~ v1_relat_1(k7_relat_1(X1,esk10_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk9_0,k1_relat_1(esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk11_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(k7_relat_1(X1,esk10_0),esk9_0) = k1_funct_1(X1,esk9_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_13])).

cnf(c_0_31,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk3_3(esk11_0,k1_relat_1(esk11_0),esk9_0)),k7_relat_1(esk11_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_23])])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk11_0,esk10_0),esk9_0) = k1_funct_1(esk11_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_22]),c_0_23])])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk11_0,esk9_0),k2_relat_1(k7_relat_1(esk11_0,esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk11_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_29])]),c_0_34])).

cnf(c_0_36,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_22]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:18:14 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.15/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.15/0.40  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.15/0.40  #
% 0.15/0.40  # Preprocessing time       : 0.028 s
% 0.15/0.40  # Presaturation interreduction done
% 0.15/0.40  
% 0.15/0.40  # Proof found!
% 0.15/0.40  # SZS status Theorem
% 0.15/0.40  # SZS output start CNFRefutation
% 0.15/0.40  fof(d11_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(v1_relat_1(X3)=>(X3=k7_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X4,X2)&r2_hidden(k4_tarski(X4,X5),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 0.15/0.40  fof(t73_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X1,X2))=>r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 0.15/0.40  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.15/0.40  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.15/0.40  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.15/0.40  fof(t72_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 0.15/0.40  fof(c_0_6, plain, ![X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X9,X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&(r2_hidden(k4_tarski(X9,X10),X6)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6)))&(~r2_hidden(X11,X7)|~r2_hidden(k4_tarski(X11,X12),X6)|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6)))&((~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|(~r2_hidden(esk1_3(X6,X7,X8),X7)|~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6))|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&((r2_hidden(esk1_3(X6,X7,X8),X7)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&(r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).
% 0.15/0.40  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X1,X2))=>r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2)))))), inference(assume_negation,[status(cth)],[t73_funct_1])).
% 0.15/0.40  cnf(c_0_8, plain, (r2_hidden(k4_tarski(X1,X3),X5)|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X5!=k7_relat_1(X4,X2)|~v1_relat_1(X5)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.15/0.40  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk11_0)&v1_funct_1(esk11_0))&((r2_hidden(esk9_0,k1_relat_1(esk11_0))&r2_hidden(esk9_0,esk10_0))&~r2_hidden(k1_funct_1(esk11_0,esk9_0),k2_relat_1(k7_relat_1(esk11_0,esk10_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.15/0.40  fof(c_0_10, plain, ![X15, X16, X17, X19, X20, X21, X22, X24]:(((~r2_hidden(X17,X16)|r2_hidden(k4_tarski(X17,esk3_3(X15,X16,X17)),X15)|X16!=k1_relat_1(X15))&(~r2_hidden(k4_tarski(X19,X20),X15)|r2_hidden(X19,X16)|X16!=k1_relat_1(X15)))&((~r2_hidden(esk4_2(X21,X22),X22)|~r2_hidden(k4_tarski(esk4_2(X21,X22),X24),X21)|X22=k1_relat_1(X21))&(r2_hidden(esk4_2(X21,X22),X22)|r2_hidden(k4_tarski(esk4_2(X21,X22),esk5_2(X21,X22)),X21)|X22=k1_relat_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.15/0.40  fof(c_0_11, plain, ![X26, X27, X28, X30, X31, X32, X34]:((((r2_hidden(esk6_3(X26,X27,X28),k1_relat_1(X26))|~r2_hidden(X28,X27)|X27!=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(X28=k1_funct_1(X26,esk6_3(X26,X27,X28))|~r2_hidden(X28,X27)|X27!=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26))))&(~r2_hidden(X31,k1_relat_1(X26))|X30!=k1_funct_1(X26,X31)|r2_hidden(X30,X27)|X27!=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26))))&((~r2_hidden(esk7_2(X26,X32),X32)|(~r2_hidden(X34,k1_relat_1(X26))|esk7_2(X26,X32)!=k1_funct_1(X26,X34))|X32=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&((r2_hidden(esk8_2(X26,X32),k1_relat_1(X26))|r2_hidden(esk7_2(X26,X32),X32)|X32=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(esk7_2(X26,X32)=k1_funct_1(X26,esk8_2(X26,X32))|r2_hidden(esk7_2(X26,X32),X32)|X32=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.15/0.40  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~v1_relat_1(k7_relat_1(X3,X4))|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_8])).
% 0.15/0.40  cnf(c_0_13, negated_conjecture, (r2_hidden(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.40  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.40  fof(c_0_15, plain, ![X36, X37]:((v1_relat_1(k7_relat_1(X36,X37))|(~v1_relat_1(X36)|~v1_funct_1(X36)))&(v1_funct_1(k7_relat_1(X36,X37))|(~v1_relat_1(X36)|~v1_funct_1(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.15/0.40  fof(c_0_16, plain, ![X38, X39, X40]:(~v1_relat_1(X40)|~v1_funct_1(X40)|(~r2_hidden(X38,X39)|k1_funct_1(k7_relat_1(X40,X39),X38)=k1_funct_1(X40,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).
% 0.15/0.40  cnf(c_0_17, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.40  cnf(c_0_18, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.40  cnf(c_0_19, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,X1),k7_relat_1(X2,esk10_0))|~r2_hidden(k4_tarski(esk9_0,X1),X2)|~v1_relat_1(k7_relat_1(X2,esk10_0))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.15/0.40  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_14])).
% 0.15/0.40  cnf(c_0_21, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.40  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.40  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.40  cnf(c_0_24, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.40  cnf(c_0_25, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).
% 0.15/0.40  cnf(c_0_26, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_18])).
% 0.15/0.40  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk3_3(X1,k1_relat_1(X1),esk9_0)),k7_relat_1(X1,esk10_0))|~r2_hidden(esk9_0,k1_relat_1(X1))|~v1_relat_1(k7_relat_1(X1,esk10_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.15/0.40  cnf(c_0_28, negated_conjecture, (r2_hidden(esk9_0,k1_relat_1(esk11_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.40  cnf(c_0_29, negated_conjecture, (v1_relat_1(k7_relat_1(esk11_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.15/0.40  cnf(c_0_30, negated_conjecture, (k1_funct_1(k7_relat_1(X1,esk10_0),esk9_0)=k1_funct_1(X1,esk9_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_13])).
% 0.15/0.40  cnf(c_0_31, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.15/0.40  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk3_3(esk11_0,k1_relat_1(esk11_0),esk9_0)),k7_relat_1(esk11_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_23])])).
% 0.15/0.40  cnf(c_0_33, negated_conjecture, (k1_funct_1(k7_relat_1(esk11_0,esk10_0),esk9_0)=k1_funct_1(esk11_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_22]), c_0_23])])).
% 0.15/0.40  cnf(c_0_34, negated_conjecture, (~r2_hidden(k1_funct_1(esk11_0,esk9_0),k2_relat_1(k7_relat_1(esk11_0,esk10_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.40  cnf(c_0_35, negated_conjecture, (~v1_funct_1(k7_relat_1(esk11_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_29])]), c_0_34])).
% 0.15/0.40  cnf(c_0_36, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.40  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_22]), c_0_23])]), ['proof']).
% 0.15/0.40  # SZS output end CNFRefutation
% 0.15/0.40  # Proof object total steps             : 38
% 0.15/0.40  # Proof object clause steps            : 25
% 0.15/0.40  # Proof object formula steps           : 13
% 0.15/0.40  # Proof object conjectures             : 16
% 0.15/0.40  # Proof object clause conjectures      : 13
% 0.15/0.40  # Proof object formula conjectures     : 3
% 0.15/0.40  # Proof object initial clauses used    : 12
% 0.15/0.40  # Proof object initial formulas used   : 6
% 0.15/0.40  # Proof object generating inferences   : 9
% 0.15/0.40  # Proof object simplifying inferences  : 19
% 0.15/0.40  # Training examples: 0 positive, 0 negative
% 0.15/0.40  # Parsed axioms                        : 6
% 0.15/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.40  # Initial clauses                      : 24
% 0.15/0.40  # Removed in clause preprocessing      : 0
% 0.15/0.40  # Initial clauses in saturation        : 24
% 0.15/0.40  # Processed clauses                    : 103
% 0.15/0.40  # ...of these trivial                  : 0
% 0.15/0.40  # ...subsumed                          : 5
% 0.15/0.40  # ...remaining for further processing  : 98
% 0.15/0.40  # Other redundant clauses eliminated   : 9
% 0.15/0.40  # Clauses deleted for lack of memory   : 0
% 0.15/0.40  # Backward-subsumed                    : 0
% 0.15/0.40  # Backward-rewritten                   : 0
% 0.15/0.40  # Generated clauses                    : 180
% 0.15/0.40  # ...of the previous two non-trivial   : 176
% 0.15/0.40  # Contextual simplify-reflections      : 6
% 0.15/0.40  # Paramodulations                      : 172
% 0.15/0.40  # Factorizations                       : 0
% 0.15/0.40  # Equation resolutions                 : 9
% 0.15/0.40  # Propositional unsat checks           : 0
% 0.15/0.40  #    Propositional check models        : 0
% 0.15/0.40  #    Propositional check unsatisfiable : 0
% 0.15/0.40  #    Propositional clauses             : 0
% 0.15/0.40  #    Propositional clauses after purity: 0
% 0.15/0.40  #    Propositional unsat core size     : 0
% 0.15/0.40  #    Propositional preprocessing time  : 0.000
% 0.15/0.40  #    Propositional encoding time       : 0.000
% 0.15/0.40  #    Propositional solver time         : 0.000
% 0.15/0.40  #    Success case prop preproc time    : 0.000
% 0.15/0.40  #    Success case prop encoding time   : 0.000
% 0.15/0.40  #    Success case prop solver time     : 0.000
% 0.15/0.40  # Current number of processed clauses  : 66
% 0.15/0.40  #    Positive orientable unit clauses  : 19
% 0.15/0.40  #    Positive unorientable unit clauses: 0
% 0.15/0.40  #    Negative unit clauses             : 2
% 0.15/0.40  #    Non-unit-clauses                  : 45
% 0.15/0.40  # Current number of unprocessed clauses: 121
% 0.15/0.40  # ...number of literals in the above   : 496
% 0.15/0.40  # Current number of archived formulas  : 0
% 0.15/0.40  # Current number of archived clauses   : 24
% 0.15/0.40  # Clause-clause subsumption calls (NU) : 556
% 0.15/0.40  # Rec. Clause-clause subsumption calls : 228
% 0.15/0.40  # Non-unit clause-clause subsumptions  : 11
% 0.15/0.40  # Unit Clause-clause subsumption calls : 28
% 0.15/0.40  # Rewrite failures with RHS unbound    : 0
% 0.15/0.40  # BW rewrite match attempts            : 12
% 0.15/0.40  # BW rewrite match successes           : 0
% 0.15/0.40  # Condensation attempts                : 0
% 0.15/0.40  # Condensation successes               : 0
% 0.15/0.40  # Termbank termtop insertions          : 6795
% 0.15/0.40  
% 0.15/0.40  # -------------------------------------------------
% 0.15/0.40  # User time                : 0.035 s
% 0.15/0.40  # System time              : 0.005 s
% 0.15/0.40  # Total time               : 0.040 s
% 0.15/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
