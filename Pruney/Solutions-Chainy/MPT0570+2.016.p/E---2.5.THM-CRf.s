%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:41 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   50 (  61 expanded)
%              Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  132 ( 178 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t174_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k2_relat_1(X2))
          & k10_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t173_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( X1 != k1_xboole_0
            & r1_tarski(X1,k2_relat_1(X2))
            & k10_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t174_relat_1])).

fof(c_0_12,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_13,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_14,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X23,X22)
        | r1_tarski(X23,X21)
        | X22 != k1_zfmisc_1(X21) )
      & ( ~ r1_tarski(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k1_zfmisc_1(X21) )
      & ( ~ r2_hidden(esk3_2(X25,X26),X26)
        | ~ r1_tarski(esk3_2(X25,X26),X25)
        | X26 = k1_zfmisc_1(X25) )
      & ( r2_hidden(esk3_2(X25,X26),X26)
        | r1_tarski(esk3_2(X25,X26),X25)
        | X26 = k1_zfmisc_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_15,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X30,X31)
      | v1_xboole_0(X31)
      | r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_16,plain,(
    ! [X29] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X29)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_17,plain,(
    ! [X28] : ~ v1_xboole_0(k1_zfmisc_1(X28)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_18,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_xboole_0(X17,X18)
      | r1_xboole_0(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & esk4_0 != k1_xboole_0
    & r1_tarski(esk4_0,k2_relat_1(esk5_0))
    & k10_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_20,plain,(
    ! [X35,X36] :
      ( ( k10_relat_1(X36,X35) != k1_xboole_0
        | r1_xboole_0(k2_relat_1(X36),X35)
        | ~ v1_relat_1(X36) )
      & ( ~ r1_xboole_0(k2_relat_1(X36),X35)
        | k10_relat_1(X36,X35) = k1_xboole_0
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).

fof(c_0_21,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_22,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk4_0,k2_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k2_relat_1(X1),X2)
    | k10_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( k10_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

fof(c_0_37,plain,(
    ! [X19,X20] :
      ( v1_xboole_0(X20)
      | ~ r1_tarski(X20,X19)
      | ~ r1_xboole_0(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | ~ r1_xboole_0(k2_relat_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.13/0.37  # and selection function SelectNewComplexAHP.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t174_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k2_relat_1(X2)))&k10_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 0.13/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.37  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.13/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.37  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.13/0.37  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.13/0.37  fof(t173_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.13/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.37  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.13/0.37  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k2_relat_1(X2)))&k10_relat_1(X2,X1)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t174_relat_1])).
% 0.13/0.37  fof(c_0_12, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.37  fof(c_0_13, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.37  fof(c_0_14, plain, ![X21, X22, X23, X24, X25, X26]:(((~r2_hidden(X23,X22)|r1_tarski(X23,X21)|X22!=k1_zfmisc_1(X21))&(~r1_tarski(X24,X21)|r2_hidden(X24,X22)|X22!=k1_zfmisc_1(X21)))&((~r2_hidden(esk3_2(X25,X26),X26)|~r1_tarski(esk3_2(X25,X26),X25)|X26=k1_zfmisc_1(X25))&(r2_hidden(esk3_2(X25,X26),X26)|r1_tarski(esk3_2(X25,X26),X25)|X26=k1_zfmisc_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.13/0.37  fof(c_0_15, plain, ![X30, X31]:(~m1_subset_1(X30,X31)|(v1_xboole_0(X31)|r2_hidden(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.37  fof(c_0_16, plain, ![X29]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X29)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.37  fof(c_0_17, plain, ![X28]:~v1_xboole_0(k1_zfmisc_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.13/0.37  fof(c_0_18, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_xboole_0(X17,X18)|r1_xboole_0(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.13/0.37  fof(c_0_19, negated_conjecture, (v1_relat_1(esk5_0)&((esk4_0!=k1_xboole_0&r1_tarski(esk4_0,k2_relat_1(esk5_0)))&k10_relat_1(esk5_0,esk4_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.37  fof(c_0_20, plain, ![X35, X36]:((k10_relat_1(X36,X35)!=k1_xboole_0|r1_xboole_0(k2_relat_1(X36),X35)|~v1_relat_1(X36))&(~r1_xboole_0(k2_relat_1(X36),X35)|k10_relat_1(X36,X35)=k1_xboole_0|~v1_relat_1(X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).
% 0.13/0.37  fof(c_0_21, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.37  cnf(c_0_22, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_23, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_24, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_25, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_26, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_27, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_28, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (r1_tarski(esk4_0,k2_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_30, plain, (r1_xboole_0(k2_relat_1(X1),X2)|k10_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (k10_relat_1(esk5_0,esk4_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_33, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.37  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_36, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.13/0.37  fof(c_0_37, plain, ![X19, X20]:(v1_xboole_0(X20)|(~r1_tarski(X20,X19)|~r1_xboole_0(X20,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (r1_xboole_0(esk4_0,X1)|~r1_xboole_0(k2_relat_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (r1_xboole_0(k2_relat_1(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.13/0.37  cnf(c_0_40, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.37  cnf(c_0_42, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.37  cnf(c_0_43, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.37  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_40])).
% 0.13/0.37  cnf(c_0_46, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 50
% 0.13/0.37  # Proof object clause steps            : 27
% 0.13/0.37  # Proof object formula steps           : 23
% 0.13/0.37  # Proof object conjectures             : 12
% 0.13/0.37  # Proof object clause conjectures      : 9
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 15
% 0.13/0.37  # Proof object initial formulas used   : 11
% 0.13/0.37  # Proof object generating inferences   : 11
% 0.13/0.37  # Proof object simplifying inferences  : 7
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 12
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 24
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 24
% 0.13/0.37  # Processed clauses                    : 63
% 0.13/0.37  # ...of these trivial                  : 3
% 0.13/0.37  # ...subsumed                          : 8
% 0.13/0.37  # ...remaining for further processing  : 52
% 0.13/0.37  # Other redundant clauses eliminated   : 6
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 1
% 0.13/0.37  # Generated clauses                    : 154
% 0.13/0.37  # ...of the previous two non-trivial   : 136
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 146
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 8
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 49
% 0.13/0.37  #    Positive orientable unit clauses  : 13
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 34
% 0.13/0.37  # Current number of unprocessed clauses: 96
% 0.13/0.37  # ...number of literals in the above   : 324
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 1
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 81
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 65
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.37  # Unit Clause-clause subsumption calls : 26
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 9
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2687
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.031 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.035 s
% 0.13/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
