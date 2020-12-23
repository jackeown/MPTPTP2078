%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:49 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 174 expanded)
%              Number of clauses        :   38 (  74 expanded)
%              Number of leaves         :    5 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  159 ( 934 expanded)
%              Number of equality atoms :   35 ( 256 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( k1_relat_1(X1) = k1_relat_1(X2)
                & ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_1])).

fof(c_0_6,plain,(
    ! [X14,X15,X16,X18,X19,X20,X21,X23] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(k4_tarski(X16,esk3_3(X14,X15,X16)),X14)
        | X15 != k1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X18,X19),X14)
        | r2_hidden(X18,X15)
        | X15 != k1_relat_1(X14) )
      & ( ~ r2_hidden(esk4_2(X20,X21),X21)
        | ~ r2_hidden(k4_tarski(esk4_2(X20,X21),X23),X20)
        | X21 = k1_relat_1(X20) )
      & ( r2_hidden(esk4_2(X20,X21),X21)
        | r2_hidden(k4_tarski(esk4_2(X20,X21),esk5_2(X20,X21)),X20)
        | X21 = k1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(k4_tarski(X9,X10),X7)
        | r2_hidden(k4_tarski(X9,X10),X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_2(X7,X11),esk2_2(X7,X11)),X7)
        | r1_tarski(X7,X11)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X7,X11),esk2_2(X7,X11)),X11)
        | r1_tarski(X7,X11)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X30] :
      ( v1_relat_1(esk6_0)
      & v1_funct_1(esk6_0)
      & v1_relat_1(esk7_0)
      & v1_funct_1(esk7_0)
      & k1_relat_1(esk6_0) = k1_relat_1(esk7_0)
      & ( ~ r2_hidden(X30,k1_relat_1(esk6_0))
        | k1_funct_1(esk6_0,X30) = k1_funct_1(esk7_0,X30) )
      & esk6_0 != esk7_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_9,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(X25,k1_relat_1(X27))
        | ~ r2_hidden(k4_tarski(X25,X26),X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( X26 = k1_funct_1(X27,X25)
        | ~ r2_hidden(k4_tarski(X25,X26),X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( ~ r2_hidden(X25,k1_relat_1(X27))
        | X26 != k1_funct_1(X27,X25)
        | r2_hidden(k4_tarski(X25,X26),X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk7_0,X1),esk2_2(esk7_0,X1)),esk7_0)
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( X1 = k1_funct_1(esk7_0,X2)
    | ~ r2_hidden(k4_tarski(X2,X1),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_12])])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = k1_funct_1(esk7_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,X1),k1_relat_1(esk6_0))
    | r1_tarski(esk7_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk6_0,X1),esk2_2(esk6_0,X1)),esk6_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk6_0,X1)),esk6_0)
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19])])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_2(esk7_0,X1)) = esk2_2(esk7_0,X1)
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_2(esk7_0,X1)) = k1_funct_1(esk6_0,esk1_2(esk7_0,X1))
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk7_0,X1)),esk7_0)
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_15]),c_0_18]),c_0_12])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,X1),k1_relat_1(esk6_0))
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk7_0,X1),k1_funct_1(esk6_0,esk1_2(esk7_0,X1))),esk6_0)
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_2(esk7_0,X1)) = esk2_2(esk7_0,X1)
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk6_0,X1),k1_funct_1(esk7_0,esk1_2(esk6_0,X1))),esk7_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_2(esk6_0,X1)) = k1_funct_1(esk6_0,esk1_2(esk6_0,X1))
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( X1 = k1_funct_1(esk6_0,X2)
    | ~ r2_hidden(k4_tarski(X2,X1),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_21]),c_0_19])])).

fof(c_0_37,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | ~ r2_hidden(k4_tarski(esk1_2(esk7_0,X1),esk2_2(esk7_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk7_0,X1),esk2_2(esk7_0,X1)),esk6_0)
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk6_0,X1),k1_funct_1(esk6_0,esk1_2(esk6_0,X1))),esk7_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_2(esk6_0,X1)) = esk2_2(esk6_0,X1)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_25])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( esk6_0 != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ r2_hidden(k4_tarski(esk1_2(esk6_0,X1),esk2_2(esk6_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk6_0,X1),esk2_2(esk6_0,X1)),esk7_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076N
% 0.20/0.41  # and selection function SelectCQIAr.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.051 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t9_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 0.20/0.41  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.41  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.20/0.41  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(c_0_5, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2)))), inference(assume_negation,[status(cth)],[t9_funct_1])).
% 0.20/0.41  fof(c_0_6, plain, ![X14, X15, X16, X18, X19, X20, X21, X23]:(((~r2_hidden(X16,X15)|r2_hidden(k4_tarski(X16,esk3_3(X14,X15,X16)),X14)|X15!=k1_relat_1(X14))&(~r2_hidden(k4_tarski(X18,X19),X14)|r2_hidden(X18,X15)|X15!=k1_relat_1(X14)))&((~r2_hidden(esk4_2(X20,X21),X21)|~r2_hidden(k4_tarski(esk4_2(X20,X21),X23),X20)|X21=k1_relat_1(X20))&(r2_hidden(esk4_2(X20,X21),X21)|r2_hidden(k4_tarski(esk4_2(X20,X21),esk5_2(X20,X21)),X20)|X21=k1_relat_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.41  fof(c_0_7, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(k4_tarski(X9,X10),X7)|r2_hidden(k4_tarski(X9,X10),X8))|~v1_relat_1(X7))&((r2_hidden(k4_tarski(esk1_2(X7,X11),esk2_2(X7,X11)),X7)|r1_tarski(X7,X11)|~v1_relat_1(X7))&(~r2_hidden(k4_tarski(esk1_2(X7,X11),esk2_2(X7,X11)),X11)|r1_tarski(X7,X11)|~v1_relat_1(X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.20/0.41  fof(c_0_8, negated_conjecture, ![X30]:((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((k1_relat_1(esk6_0)=k1_relat_1(esk7_0)&(~r2_hidden(X30,k1_relat_1(esk6_0))|k1_funct_1(esk6_0,X30)=k1_funct_1(esk7_0,X30)))&esk6_0!=esk7_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.20/0.41  fof(c_0_9, plain, ![X25, X26, X27]:(((r2_hidden(X25,k1_relat_1(X27))|~r2_hidden(k4_tarski(X25,X26),X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(X26=k1_funct_1(X27,X25)|~r2_hidden(k4_tarski(X25,X26),X27)|(~v1_relat_1(X27)|~v1_funct_1(X27))))&(~r2_hidden(X25,k1_relat_1(X27))|X26!=k1_funct_1(X27,X25)|r2_hidden(k4_tarski(X25,X26),X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.20/0.41  cnf(c_0_10, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_11, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.41  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_14, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_15, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_16, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_17, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk7_0,X1),esk2_2(esk7_0,X1)),esk7_0)|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (k1_relat_1(esk6_0)=k1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_22, negated_conjecture, (X1=k1_funct_1(esk7_0,X2)|~r2_hidden(k4_tarski(X2,X1),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_12])])).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (k1_funct_1(esk6_0,X1)=k1_funct_1(esk7_0,X1)|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_2(esk7_0,X1),k1_relat_1(esk6_0))|r1_tarski(esk7_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk6_0,X1),esk2_2(esk6_0,X1)),esk6_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_11, c_0_19])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk6_0,X1)),esk6_0)|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_19])])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (k1_funct_1(esk7_0,esk1_2(esk7_0,X1))=esk2_2(esk7_0,X1)|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_17])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (k1_funct_1(esk7_0,esk1_2(esk7_0,X1))=k1_funct_1(esk6_0,esk1_2(esk7_0,X1))|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk7_0,X1)),esk7_0)|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_15]), c_0_18]), c_0_12])])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(esk6_0,X1),k1_relat_1(esk6_0))|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_16, c_0_25])).
% 0.20/0.41  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk7_0,X1),k1_funct_1(esk6_0,esk1_2(esk7_0,X1))),esk6_0)|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (k1_funct_1(esk6_0,esk1_2(esk7_0,X1))=esk2_2(esk7_0,X1)|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk6_0,X1),k1_funct_1(esk7_0,esk1_2(esk6_0,X1))),esk7_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (k1_funct_1(esk7_0,esk1_2(esk6_0,X1))=k1_funct_1(esk6_0,esk1_2(esk6_0,X1))|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_30])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (X1=k1_funct_1(esk6_0,X2)|~r2_hidden(k4_tarski(X2,X1),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_21]), c_0_19])])).
% 0.20/0.41  fof(c_0_37, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (r1_tarski(esk7_0,X1)|~r2_hidden(k4_tarski(esk1_2(esk7_0,X1),esk2_2(esk7_0,X1)),X1)), inference(spm,[status(thm)],[c_0_31, c_0_12])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk7_0,X1),esk2_2(esk7_0,X1)),esk6_0)|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk6_0,X1),k1_funct_1(esk6_0,esk1_2(esk6_0,X1))),esk7_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (k1_funct_1(esk6_0,esk1_2(esk6_0,X1))=esk2_2(esk6_0,X1)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_25])).
% 0.20/0.41  cnf(c_0_42, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (r1_tarski(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (esk6_0!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (r1_tarski(esk6_0,X1)|~r2_hidden(k4_tarski(esk1_2(esk6_0,X1),esk2_2(esk6_0,X1)),X1)), inference(spm,[status(thm)],[c_0_31, c_0_19])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk6_0,X1),esk2_2(esk6_0,X1)),esk7_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (~r1_tarski(esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 49
% 0.20/0.41  # Proof object clause steps            : 38
% 0.20/0.41  # Proof object formula steps           : 11
% 0.20/0.41  # Proof object conjectures             : 33
% 0.20/0.41  # Proof object clause conjectures      : 30
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 13
% 0.20/0.41  # Proof object initial formulas used   : 5
% 0.20/0.41  # Proof object generating inferences   : 23
% 0.20/0.41  # Proof object simplifying inferences  : 14
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 5
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 20
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 20
% 0.20/0.41  # Processed clauses                    : 102
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 21
% 0.20/0.41  # ...remaining for further processing  : 81
% 0.20/0.41  # Other redundant clauses eliminated   : 5
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 1
% 0.20/0.41  # Backward-rewritten                   : 0
% 0.20/0.41  # Generated clauses                    : 124
% 0.20/0.41  # ...of the previous two non-trivial   : 112
% 0.20/0.41  # Contextual simplify-reflections      : 0
% 0.20/0.41  # Paramodulations                      : 115
% 0.20/0.41  # Factorizations                       : 4
% 0.20/0.41  # Equation resolutions                 : 5
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 57
% 0.20/0.41  #    Positive orientable unit clauses  : 7
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 2
% 0.20/0.41  #    Non-unit-clauses                  : 48
% 0.20/0.41  # Current number of unprocessed clauses: 47
% 0.20/0.41  # ...number of literals in the above   : 133
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 19
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 106
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 93
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 22
% 0.20/0.41  # Unit Clause-clause subsumption calls : 10
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 0
% 0.20/0.41  # BW rewrite match successes           : 0
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 4171
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.058 s
% 0.20/0.41  # System time              : 0.005 s
% 0.20/0.41  # Total time               : 0.064 s
% 0.20/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
