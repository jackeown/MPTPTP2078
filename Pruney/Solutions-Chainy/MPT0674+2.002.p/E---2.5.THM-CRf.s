%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 146 expanded)
%              Number of clauses        :   38 (  63 expanded)
%              Number of leaves         :    6 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  161 ( 478 expanded)
%              Number of equality atoms :   59 ( 176 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t117_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_6,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | k11_relat_1(X14,X15) = k9_relat_1(X14,k1_tarski(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_7,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t117_funct_1])).

cnf(c_0_9,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & r2_hidden(esk6_0,k1_relat_1(esk7_0))
    & k11_relat_1(esk7_0,esk6_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_12,plain,(
    ! [X6,X7,X8,X9,X10,X11] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X6
        | X7 != k1_tarski(X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k1_tarski(X6) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) != X10
        | X11 = k1_tarski(X10) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) = X10
        | X11 = k1_tarski(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X16,X17,X18,X20] :
      ( ( r2_hidden(esk2_3(X16,X17,X18),k1_relat_1(X18))
        | ~ r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk2_3(X16,X17,X18),X16),X18)
        | ~ r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(X20,k1_relat_1(X18))
        | ~ r2_hidden(k4_tarski(X20,X16),X18)
        | ~ r2_hidden(X20,X17)
        | r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_14,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k2_tarski(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X33,k1_relat_1(X35))
        | ~ r2_hidden(k4_tarski(X33,X34),X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( X34 = k1_funct_1(X35,X33)
        | ~ r2_hidden(k4_tarski(X33,X34),X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(X33,k1_relat_1(X35))
        | X34 != k1_funct_1(X35,X33)
        | r2_hidden(k4_tarski(X33,X34),X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k9_relat_1(esk7_0,k2_tarski(X1,X1)) = k11_relat_1(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_3(X1,k2_tarski(X2,X2),esk7_0),X1),esk7_0)
    | ~ r2_hidden(X1,k11_relat_1(esk7_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15])])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk2_3(X1,k2_tarski(X2,X2),esk7_0),k2_tarski(X2,X2))
    | ~ r2_hidden(X1,k11_relat_1(esk7_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_15])])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk7_0,esk2_3(X1,k2_tarski(X2,X2),esk7_0)) = X1
    | ~ r2_hidden(X1,k11_relat_1(esk7_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_15])])).

cnf(c_0_29,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk1_2(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( esk2_3(X1,k2_tarski(X2,X2),esk7_0) = X2
    | ~ r2_hidden(X1,k11_relat_1(esk7_0,X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk7_0,esk2_3(esk1_2(X1,k11_relat_1(esk7_0,X2)),k2_tarski(X2,X2),esk7_0)) = esk1_2(X1,k11_relat_1(esk7_0,X2))
    | esk1_2(X1,k11_relat_1(esk7_0,X2)) = X1
    | k11_relat_1(esk7_0,X2) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( esk2_3(esk1_2(X1,k11_relat_1(esk7_0,X2)),k2_tarski(X2,X2),esk7_0) = X2
    | esk1_2(X1,k11_relat_1(esk7_0,X2)) = X1
    | k11_relat_1(esk7_0,X2) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_10])).

cnf(c_0_35,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( esk1_2(X1,k11_relat_1(esk7_0,X2)) = k1_funct_1(esk7_0,X2)
    | k11_relat_1(esk7_0,X2) = k2_tarski(X1,X1)
    | esk1_2(X1,k11_relat_1(esk7_0,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( esk1_2(k1_funct_1(esk7_0,X1),k11_relat_1(esk7_0,X1)) = k1_funct_1(esk7_0,X1)
    | k2_tarski(k1_funct_1(esk7_0,X1),k1_funct_1(esk7_0,X1)) = k11_relat_1(esk7_0,X1) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_36])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k9_relat_1(X2,k2_tarski(X3,X3)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X3,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k11_relat_1(esk7_0,esk6_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,negated_conjecture,
    ( k2_tarski(k1_funct_1(esk7_0,X1),k1_funct_1(esk7_0,X1)) = k11_relat_1(esk7_0,X1)
    | ~ r2_hidden(k1_funct_1(esk7_0,X1),k11_relat_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,k11_relat_1(esk7_0,esk6_0))
    | ~ r2_hidden(k4_tarski(esk6_0,X1),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_19]),c_0_15])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,k1_funct_1(esk7_0,esk6_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_24]),c_0_15])])).

cnf(c_0_49,negated_conjecture,
    ( k11_relat_1(esk7_0,esk6_0) != k2_tarski(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_10])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.19/0.51  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.028 s
% 0.19/0.51  # Presaturation interreduction done
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.19/0.51  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.51  fof(t117_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 0.19/0.51  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.51  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.19/0.51  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.19/0.51  fof(c_0_6, plain, ![X14, X15]:(~v1_relat_1(X14)|k11_relat_1(X14,X15)=k9_relat_1(X14,k1_tarski(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.19/0.51  fof(c_0_7, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.51  fof(c_0_8, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t117_funct_1])).
% 0.19/0.51  cnf(c_0_9, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.51  cnf(c_0_10, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.51  fof(c_0_11, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&(r2_hidden(esk6_0,k1_relat_1(esk7_0))&k11_relat_1(esk7_0,esk6_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.51  fof(c_0_12, plain, ![X6, X7, X8, X9, X10, X11]:(((~r2_hidden(X8,X7)|X8=X6|X7!=k1_tarski(X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k1_tarski(X6)))&((~r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)!=X10|X11=k1_tarski(X10))&(r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)=X10|X11=k1_tarski(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.51  fof(c_0_13, plain, ![X16, X17, X18, X20]:((((r2_hidden(esk2_3(X16,X17,X18),k1_relat_1(X18))|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk2_3(X16,X17,X18),X16),X18)|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18)))&(r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18)))&(~r2_hidden(X20,k1_relat_1(X18))|~r2_hidden(k4_tarski(X20,X16),X18)|~r2_hidden(X20,X17)|r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.19/0.51  cnf(c_0_14, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k2_tarski(X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.51  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  cnf(c_0_16, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.51  fof(c_0_17, plain, ![X33, X34, X35]:(((r2_hidden(X33,k1_relat_1(X35))|~r2_hidden(k4_tarski(X33,X34),X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(X34=k1_funct_1(X35,X33)|~r2_hidden(k4_tarski(X33,X34),X35)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(~r2_hidden(X33,k1_relat_1(X35))|X34!=k1_funct_1(X35,X33)|r2_hidden(k4_tarski(X33,X34),X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.19/0.51  cnf(c_0_18, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.51  cnf(c_0_19, negated_conjecture, (k9_relat_1(esk7_0,k2_tarski(X1,X1))=k11_relat_1(esk7_0,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.51  cnf(c_0_20, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_10])).
% 0.19/0.51  cnf(c_0_21, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.51  cnf(c_0_22, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.51  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(esk2_3(X1,k2_tarski(X2,X2),esk7_0),X1),esk7_0)|~r2_hidden(X1,k11_relat_1(esk7_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_15])])).
% 0.19/0.51  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.51  cnf(c_0_26, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.51  cnf(c_0_27, negated_conjecture, (r2_hidden(esk2_3(X1,k2_tarski(X2,X2),esk7_0),k2_tarski(X2,X2))|~r2_hidden(X1,k11_relat_1(esk7_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_19]), c_0_15])])).
% 0.19/0.51  cnf(c_0_28, negated_conjecture, (k1_funct_1(esk7_0,esk2_3(X1,k2_tarski(X2,X2),esk7_0))=X1|~r2_hidden(X1,k11_relat_1(esk7_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_15])])).
% 0.19/0.51  cnf(c_0_29, plain, (X2=k2_tarski(X1,X1)|esk1_2(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_25, c_0_10])).
% 0.19/0.51  cnf(c_0_30, negated_conjecture, (esk2_3(X1,k2_tarski(X2,X2),esk7_0)=X2|~r2_hidden(X1,k11_relat_1(esk7_0,X2))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.51  cnf(c_0_31, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.51  cnf(c_0_32, negated_conjecture, (k1_funct_1(esk7_0,esk2_3(esk1_2(X1,k11_relat_1(esk7_0,X2)),k2_tarski(X2,X2),esk7_0))=esk1_2(X1,k11_relat_1(esk7_0,X2))|esk1_2(X1,k11_relat_1(esk7_0,X2))=X1|k11_relat_1(esk7_0,X2)=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.51  cnf(c_0_33, negated_conjecture, (esk2_3(esk1_2(X1,k11_relat_1(esk7_0,X2)),k2_tarski(X2,X2),esk7_0)=X2|esk1_2(X1,k11_relat_1(esk7_0,X2))=X1|k11_relat_1(esk7_0,X2)=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.19/0.51  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_31, c_0_10])).
% 0.19/0.51  cnf(c_0_35, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.51  cnf(c_0_36, negated_conjecture, (esk1_2(X1,k11_relat_1(esk7_0,X2))=k1_funct_1(esk7_0,X2)|k11_relat_1(esk7_0,X2)=k2_tarski(X1,X1)|esk1_2(X1,k11_relat_1(esk7_0,X2))=X1), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.51  cnf(c_0_37, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.51  cnf(c_0_38, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).
% 0.19/0.51  cnf(c_0_39, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.51  cnf(c_0_40, plain, (X2=k2_tarski(X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_35, c_0_10])).
% 0.19/0.51  cnf(c_0_41, negated_conjecture, (esk1_2(k1_funct_1(esk7_0,X1),k11_relat_1(esk7_0,X1))=k1_funct_1(esk7_0,X1)|k2_tarski(k1_funct_1(esk7_0,X1),k1_funct_1(esk7_0,X1))=k11_relat_1(esk7_0,X1)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_36])])).
% 0.19/0.51  cnf(c_0_42, plain, (r2_hidden(X1,k9_relat_1(X2,k2_tarski(X3,X3)))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X3,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.51  cnf(c_0_43, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  cnf(c_0_44, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_39])).
% 0.19/0.51  cnf(c_0_45, negated_conjecture, (k11_relat_1(esk7_0,esk6_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  cnf(c_0_46, negated_conjecture, (k2_tarski(k1_funct_1(esk7_0,X1),k1_funct_1(esk7_0,X1))=k11_relat_1(esk7_0,X1)|~r2_hidden(k1_funct_1(esk7_0,X1),k11_relat_1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.51  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,k11_relat_1(esk7_0,esk6_0))|~r2_hidden(k4_tarski(esk6_0,X1),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_19]), c_0_15])])).
% 0.19/0.51  cnf(c_0_48, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,k1_funct_1(esk7_0,esk6_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_43]), c_0_24]), c_0_15])])).
% 0.19/0.51  cnf(c_0_49, negated_conjecture, (k11_relat_1(esk7_0,esk6_0)!=k2_tarski(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0))), inference(rw,[status(thm)],[c_0_45, c_0_10])).
% 0.19/0.51  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])]), c_0_49]), ['proof']).
% 0.19/0.51  # SZS output end CNFRefutation
% 0.19/0.51  # Proof object total steps             : 51
% 0.19/0.51  # Proof object clause steps            : 38
% 0.19/0.51  # Proof object formula steps           : 13
% 0.19/0.51  # Proof object conjectures             : 21
% 0.19/0.51  # Proof object clause conjectures      : 18
% 0.19/0.51  # Proof object formula conjectures     : 3
% 0.19/0.51  # Proof object initial clauses used    : 15
% 0.19/0.51  # Proof object initial formulas used   : 6
% 0.19/0.51  # Proof object generating inferences   : 14
% 0.19/0.51  # Proof object simplifying inferences  : 27
% 0.19/0.51  # Training examples: 0 positive, 0 negative
% 0.19/0.51  # Parsed axioms                        : 7
% 0.19/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.51  # Initial clauses                      : 25
% 0.19/0.51  # Removed in clause preprocessing      : 1
% 0.19/0.51  # Initial clauses in saturation        : 24
% 0.19/0.51  # Processed clauses                    : 696
% 0.19/0.51  # ...of these trivial                  : 4
% 0.19/0.51  # ...subsumed                          : 245
% 0.19/0.51  # ...remaining for further processing  : 447
% 0.19/0.51  # Other redundant clauses eliminated   : 66
% 0.19/0.51  # Clauses deleted for lack of memory   : 0
% 0.19/0.51  # Backward-subsumed                    : 8
% 0.19/0.51  # Backward-rewritten                   : 4
% 0.19/0.51  # Generated clauses                    : 3150
% 0.19/0.51  # ...of the previous two non-trivial   : 2901
% 0.19/0.51  # Contextual simplify-reflections      : 2
% 0.19/0.51  # Paramodulations                      : 2978
% 0.19/0.51  # Factorizations                       : 85
% 0.19/0.51  # Equation resolutions                 : 89
% 0.19/0.51  # Propositional unsat checks           : 0
% 0.19/0.51  #    Propositional check models        : 0
% 0.19/0.51  #    Propositional check unsatisfiable : 0
% 0.19/0.51  #    Propositional clauses             : 0
% 0.19/0.51  #    Propositional clauses after purity: 0
% 0.19/0.51  #    Propositional unsat core size     : 0
% 0.19/0.51  #    Propositional preprocessing time  : 0.000
% 0.19/0.51  #    Propositional encoding time       : 0.000
% 0.19/0.51  #    Propositional solver time         : 0.000
% 0.19/0.51  #    Success case prop preproc time    : 0.000
% 0.19/0.51  #    Success case prop encoding time   : 0.000
% 0.19/0.51  #    Success case prop solver time     : 0.000
% 0.19/0.51  # Current number of processed clauses  : 404
% 0.19/0.51  #    Positive orientable unit clauses  : 22
% 0.19/0.51  #    Positive unorientable unit clauses: 0
% 0.19/0.51  #    Negative unit clauses             : 1
% 0.19/0.51  #    Non-unit-clauses                  : 381
% 0.19/0.51  # Current number of unprocessed clauses: 2225
% 0.19/0.51  # ...number of literals in the above   : 13482
% 0.19/0.51  # Current number of archived formulas  : 0
% 0.19/0.51  # Current number of archived clauses   : 37
% 0.19/0.51  # Clause-clause subsumption calls (NU) : 61621
% 0.19/0.51  # Rec. Clause-clause subsumption calls : 13575
% 0.19/0.51  # Non-unit clause-clause subsumptions  : 210
% 0.19/0.51  # Unit Clause-clause subsumption calls : 219
% 0.19/0.51  # Rewrite failures with RHS unbound    : 0
% 0.19/0.51  # BW rewrite match attempts            : 23
% 0.19/0.51  # BW rewrite match successes           : 4
% 0.19/0.51  # Condensation attempts                : 0
% 0.19/0.51  # Condensation successes               : 0
% 0.19/0.51  # Termbank termtop insertions          : 141622
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.168 s
% 0.19/0.52  # System time              : 0.008 s
% 0.19/0.52  # Total time               : 0.175 s
% 0.19/0.52  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
