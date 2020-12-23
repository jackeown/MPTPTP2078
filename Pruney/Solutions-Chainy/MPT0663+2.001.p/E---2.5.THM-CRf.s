%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:12 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   49 (  85 expanded)
%              Number of clauses        :   30 (  39 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 281 expanded)
%              Number of equality atoms :   55 ( 111 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t71_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(t70_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(c_0_9,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X25,X24)
        | X25 = X20
        | X25 = X21
        | X25 = X22
        | X25 = X23
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( X26 != X20
        | r2_hidden(X26,X24)
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( X26 != X21
        | r2_hidden(X26,X24)
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( X26 != X22
        | r2_hidden(X26,X24)
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( X26 != X23
        | r2_hidden(X26,X24)
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( esk2_5(X27,X28,X29,X30,X31) != X27
        | ~ r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)
        | X31 = k2_enumset1(X27,X28,X29,X30) )
      & ( esk2_5(X27,X28,X29,X30,X31) != X28
        | ~ r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)
        | X31 = k2_enumset1(X27,X28,X29,X30) )
      & ( esk2_5(X27,X28,X29,X30,X31) != X29
        | ~ r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)
        | X31 = k2_enumset1(X27,X28,X29,X30) )
      & ( esk2_5(X27,X28,X29,X30,X31) != X30
        | ~ r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)
        | X31 = k2_enumset1(X27,X28,X29,X30) )
      & ( r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)
        | esk2_5(X27,X28,X29,X30,X31) = X27
        | esk2_5(X27,X28,X29,X30,X31) = X28
        | esk2_5(X27,X28,X29,X30,X31) = X29
        | esk2_5(X27,X28,X29,X30,X31) = X30
        | X31 = k2_enumset1(X27,X28,X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_11,plain,(
    ! [X35,X36] :
      ( ~ r2_hidden(X35,X36)
      | r1_tarski(k1_setfam_1(X36),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X4,X5,X1) ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
         => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t71_funct_1])).

fof(c_0_14,plain,(
    ! [X33,X34] : k1_setfam_1(k2_tarski(X33,X34)) = k3_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X4,X1)) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r2_hidden(esk3_0,k3_xboole_0(k1_relat_1(esk5_0),esk4_0))
    & k1_funct_1(k7_relat_1(esk5_0,esk4_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X4,X1,X5) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X37,X38,X39] :
      ( ( r2_hidden(X37,X38)
        | ~ r2_hidden(X37,k1_relat_1(k7_relat_1(X39,X38)))
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(X37,k1_relat_1(X39))
        | ~ r2_hidden(X37,k1_relat_1(k7_relat_1(X39,X38)))
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(X37,X38)
        | ~ r2_hidden(X37,k1_relat_1(X39))
        | r2_hidden(X37,k1_relat_1(k7_relat_1(X39,X38)))
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X2,X3,X4)),X4) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(k1_relat_1(esk5_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X1,X4)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X4,X5,X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_0,k1_setfam_1(k2_enumset1(k1_relat_1(esk5_0),k1_relat_1(esk5_0),k1_relat_1(esk5_0),esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X2,X3,X4)),X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_31])).

fof(c_0_37,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ v1_funct_1(X42)
      | ~ r2_hidden(X40,k1_relat_1(k7_relat_1(X42,X41)))
      | k1_funct_1(k7_relat_1(X42,X41),X40) = k1_funct_1(X42,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(esk5_0,X2)))
    | ~ r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X4,X2,X5))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_41,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(k7_relat_1(esk5_0,esk4_0)))
    | ~ r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk5_0,X1),X2) = k1_funct_1(esk5_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(esk5_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_33])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(k7_relat_1(esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk5_0,esk4_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n018.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.14/0.37  # and selection function SelectNegativeLiterals.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(d2_enumset1, axiom, ![X1, X2, X3, X4, X5]:(X5=k2_enumset1(X1,X2,X3,X4)<=>![X6]:(r2_hidden(X6,X5)<=>~((((X6!=X1&X6!=X2)&X6!=X3)&X6!=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 0.14/0.37  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.14/0.37  fof(t71_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 0.14/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.37  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 0.14/0.37  fof(t70_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 0.14/0.37  fof(c_0_9, plain, ![X20, X21, X22, X23, X24, X25, X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X25,X24)|(X25=X20|X25=X21|X25=X22|X25=X23)|X24!=k2_enumset1(X20,X21,X22,X23))&((((X26!=X20|r2_hidden(X26,X24)|X24!=k2_enumset1(X20,X21,X22,X23))&(X26!=X21|r2_hidden(X26,X24)|X24!=k2_enumset1(X20,X21,X22,X23)))&(X26!=X22|r2_hidden(X26,X24)|X24!=k2_enumset1(X20,X21,X22,X23)))&(X26!=X23|r2_hidden(X26,X24)|X24!=k2_enumset1(X20,X21,X22,X23))))&(((((esk2_5(X27,X28,X29,X30,X31)!=X27|~r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)|X31=k2_enumset1(X27,X28,X29,X30))&(esk2_5(X27,X28,X29,X30,X31)!=X28|~r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)|X31=k2_enumset1(X27,X28,X29,X30)))&(esk2_5(X27,X28,X29,X30,X31)!=X29|~r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)|X31=k2_enumset1(X27,X28,X29,X30)))&(esk2_5(X27,X28,X29,X30,X31)!=X30|~r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)|X31=k2_enumset1(X27,X28,X29,X30)))&(r2_hidden(esk2_5(X27,X28,X29,X30,X31),X31)|(esk2_5(X27,X28,X29,X30,X31)=X27|esk2_5(X27,X28,X29,X30,X31)=X28|esk2_5(X27,X28,X29,X30,X31)=X29|esk2_5(X27,X28,X29,X30,X31)=X30)|X31=k2_enumset1(X27,X28,X29,X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).
% 0.14/0.37  cnf(c_0_10, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  fof(c_0_11, plain, ![X35, X36]:(~r2_hidden(X35,X36)|r1_tarski(k1_setfam_1(X36),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.14/0.37  cnf(c_0_12, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X4,X5,X1)), inference(er,[status(thm)],[c_0_10])).
% 0.14/0.37  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1)))), inference(assume_negation,[status(cth)],[t71_funct_1])).
% 0.14/0.37  fof(c_0_14, plain, ![X33, X34]:k1_setfam_1(k2_tarski(X33,X34))=k3_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.37  fof(c_0_15, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.37  cnf(c_0_16, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X5,X2,X6)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  fof(c_0_17, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.37  cnf(c_0_18, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_19, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X4,X1))), inference(er,[status(thm)],[c_0_12])).
% 0.14/0.37  fof(c_0_20, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(r2_hidden(esk3_0,k3_xboole_0(k1_relat_1(esk5_0),esk4_0))&k1_funct_1(k7_relat_1(esk5_0,esk4_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.14/0.37  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  fof(c_0_23, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.37  cnf(c_0_24, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X4,X1,X5)), inference(er,[status(thm)],[c_0_16])).
% 0.14/0.37  fof(c_0_25, plain, ![X37, X38, X39]:(((r2_hidden(X37,X38)|~r2_hidden(X37,k1_relat_1(k7_relat_1(X39,X38)))|~v1_relat_1(X39))&(r2_hidden(X37,k1_relat_1(X39))|~r2_hidden(X37,k1_relat_1(k7_relat_1(X39,X38)))|~v1_relat_1(X39)))&(~r2_hidden(X37,X38)|~r2_hidden(X37,k1_relat_1(X39))|r2_hidden(X37,k1_relat_1(k7_relat_1(X39,X38)))|~v1_relat_1(X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.14/0.37  cnf(c_0_26, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_27, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X2,X3,X4)),X4)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk3_0,k3_xboole_0(k1_relat_1(esk5_0),esk4_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_29, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.37  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_31, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X1,X4))), inference(er,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_32, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X4,X5,X2)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (r2_hidden(esk3_0,k1_setfam_1(k2_enumset1(k1_relat_1(esk5_0),k1_relat_1(esk5_0),k1_relat_1(esk5_0),esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.14/0.37  cnf(c_0_36, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X2,X3,X4)),X3)), inference(spm,[status(thm)],[c_0_18, c_0_31])).
% 0.14/0.37  fof(c_0_37, plain, ![X40, X41, X42]:(~v1_relat_1(X42)|~v1_funct_1(X42)|(~r2_hidden(X40,k1_relat_1(k7_relat_1(X42,X41)))|k1_funct_1(k7_relat_1(X42,X41),X40)=k1_funct_1(X42,X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).
% 0.14/0.37  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,k1_relat_1(k7_relat_1(esk5_0,X2)))|~r2_hidden(X1,k1_relat_1(esk5_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.37  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.37  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X4,X2,X5)))), inference(spm,[status(thm)],[c_0_26, c_0_36])).
% 0.14/0.37  cnf(c_0_41, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.37  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(k7_relat_1(esk5_0,esk4_0)))|~r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.14/0.37  cnf(c_0_44, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 0.14/0.37  cnf(c_0_45, negated_conjecture, (k1_funct_1(k7_relat_1(esk5_0,X1),X2)=k1_funct_1(esk5_0,X2)|~r2_hidden(X2,k1_relat_1(k7_relat_1(esk5_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_33])])).
% 0.14/0.37  cnf(c_0_46, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(k7_relat_1(esk5_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.14/0.37  cnf(c_0_47, negated_conjecture, (k1_funct_1(k7_relat_1(esk5_0,esk4_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 49
% 0.14/0.37  # Proof object clause steps            : 30
% 0.14/0.37  # Proof object formula steps           : 19
% 0.14/0.37  # Proof object conjectures             : 15
% 0.14/0.37  # Proof object clause conjectures      : 12
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 13
% 0.14/0.37  # Proof object initial formulas used   : 9
% 0.14/0.37  # Proof object generating inferences   : 12
% 0.14/0.37  # Proof object simplifying inferences  : 10
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 10
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 26
% 0.14/0.37  # Removed in clause preprocessing      : 3
% 0.14/0.37  # Initial clauses in saturation        : 23
% 0.14/0.37  # Processed clauses                    : 97
% 0.14/0.37  # ...of these trivial                  : 4
% 0.14/0.37  # ...subsumed                          : 11
% 0.14/0.37  # ...remaining for further processing  : 82
% 0.14/0.37  # Other redundant clauses eliminated   : 28
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 2
% 0.14/0.37  # Generated clauses                    : 147
% 0.14/0.37  # ...of the previous two non-trivial   : 109
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 101
% 0.14/0.37  # Factorizations                       : 12
% 0.14/0.37  # Equation resolutions                 : 34
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 53
% 0.14/0.37  #    Positive orientable unit clauses  : 16
% 0.14/0.37  #    Positive unorientable unit clauses: 1
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 35
% 0.14/0.37  # Current number of unprocessed clauses: 55
% 0.14/0.37  # ...number of literals in the above   : 212
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 28
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 284
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 270
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 11
% 0.14/0.37  # Unit Clause-clause subsumption calls : 77
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 17
% 0.14/0.37  # BW rewrite match successes           : 5
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 3103
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.029 s
% 0.14/0.37  # System time              : 0.006 s
% 0.14/0.37  # Total time               : 0.035 s
% 0.14/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
