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
% DateTime   : Thu Dec  3 10:48:08 EST 2020

% Result     : Theorem 0.34s
% Output     : CNFRefutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 304 expanded)
%              Number of clauses        :   37 ( 149 expanded)
%              Number of leaves         :   10 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 653 expanded)
%              Number of equality atoms :   20 ( 184 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t14_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_10,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X30,X31] :
      ( ( ~ m1_subset_1(X30,k1_zfmisc_1(X31))
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(X30,X31)
        | m1_subset_1(X30,k1_zfmisc_1(X31)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_14,plain,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_15,plain,(
    ! [X25,X26] : r1_tarski(X25,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_16,plain,(
    ! [X16,X17,X18] : r1_tarski(k2_xboole_0(k3_xboole_0(X16,X17),k3_xboole_0(X16,X18)),k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t14_relat_1])).

fof(c_0_20,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | v1_relat_1(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_26,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X34)
      | ~ v1_relat_1(X35)
      | k1_relat_1(k2_xboole_0(X34,X35)) = k2_xboole_0(k1_relat_1(X34),k1_relat_1(X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & ~ r1_tarski(k1_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_28,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_25])).

fof(c_0_32,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X13,X15)
      | r1_tarski(X13,k3_xboole_0(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_33,plain,
    ( k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_17,c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk2_0)) = k1_relat_1(k2_xboole_0(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(esk2_0,X1)),k1_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk1_0)) = k1_relat_1(k2_xboole_0(X1,esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(k3_xboole_0(X1,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k1_relat_1(k3_xboole_0(esk2_0,X1)),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(X1,esk1_0)),k1_relat_1(esk1_0)) = k1_relat_1(esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_49])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k1_relat_1(k3_xboole_0(esk2_0,X1)),k3_xboole_0(X2,k1_relat_1(esk2_0)))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(esk2_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_relat_1(k3_xboole_0(X1,esk1_0)),k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k1_relat_1(esk2_0),k1_relat_1(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_53]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.34/0.53  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.34/0.53  # and selection function SelectDiffNegLit.
% 0.34/0.53  #
% 0.34/0.53  # Preprocessing time       : 0.038 s
% 0.34/0.53  # Presaturation interreduction done
% 0.34/0.53  
% 0.34/0.53  # Proof found!
% 0.34/0.53  # SZS status Theorem
% 0.34/0.53  # SZS output start CNFRefutation
% 0.34/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.34/0.53  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.34/0.53  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.34/0.53  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.34/0.53  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.34/0.53  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.34/0.53  fof(t14_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relat_1)).
% 0.34/0.53  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.34/0.53  fof(t13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 0.34/0.53  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.34/0.53  fof(c_0_10, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.34/0.53  fof(c_0_11, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.34/0.53  cnf(c_0_12, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.34/0.53  fof(c_0_13, plain, ![X30, X31]:((~m1_subset_1(X30,k1_zfmisc_1(X31))|r1_tarski(X30,X31))&(~r1_tarski(X30,X31)|m1_subset_1(X30,k1_zfmisc_1(X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.34/0.53  fof(c_0_14, plain, ![X11, X12]:r1_tarski(k3_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.34/0.53  fof(c_0_15, plain, ![X25, X26]:r1_tarski(X25,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.34/0.53  fof(c_0_16, plain, ![X16, X17, X18]:r1_tarski(k2_xboole_0(k3_xboole_0(X16,X17),k3_xboole_0(X16,X18)),k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.34/0.53  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.34/0.53  cnf(c_0_18, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_12])).
% 0.34/0.53  fof(c_0_19, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t14_relat_1])).
% 0.34/0.53  fof(c_0_20, plain, ![X32, X33]:(~v1_relat_1(X32)|(~m1_subset_1(X33,k1_zfmisc_1(X32))|v1_relat_1(X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.34/0.53  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.34/0.53  cnf(c_0_22, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.34/0.53  cnf(c_0_23, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.34/0.53  cnf(c_0_24, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.34/0.53  cnf(c_0_25, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.34/0.53  fof(c_0_26, plain, ![X34, X35]:(~v1_relat_1(X34)|(~v1_relat_1(X35)|k1_relat_1(k2_xboole_0(X34,X35))=k2_xboole_0(k1_relat_1(X34),k1_relat_1(X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).
% 0.34/0.53  fof(c_0_27, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&~r1_tarski(k1_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.34/0.53  cnf(c_0_28, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.34/0.53  cnf(c_0_29, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.34/0.53  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_21, c_0_23])).
% 0.34/0.53  cnf(c_0_31, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_25])).
% 0.34/0.53  fof(c_0_32, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X13,X15)|r1_tarski(X13,k3_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.34/0.53  cnf(c_0_33, plain, (k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.34/0.53  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.34/0.53  cnf(c_0_35, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.34/0.53  cnf(c_0_36, plain, (v1_relat_1(X1)|~v1_relat_1(k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.34/0.53  cnf(c_0_37, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X2)=X2), inference(spm,[status(thm)],[c_0_17, c_0_31])).
% 0.34/0.53  cnf(c_0_38, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.34/0.53  cnf(c_0_39, negated_conjecture, (k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk2_0))=k1_relat_1(k2_xboole_0(X1,esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.34/0.53  cnf(c_0_40, negated_conjecture, (v1_relat_1(k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.34/0.53  cnf(c_0_41, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 0.34/0.53  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.34/0.53  cnf(c_0_43, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.34/0.53  cnf(c_0_44, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_38, c_0_22])).
% 0.34/0.53  cnf(c_0_45, negated_conjecture, (k2_xboole_0(k1_relat_1(k3_xboole_0(esk2_0,X1)),k1_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.34/0.53  cnf(c_0_46, negated_conjecture, (k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk1_0))=k1_relat_1(k2_xboole_0(X1,esk1_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_42])).
% 0.34/0.53  cnf(c_0_47, negated_conjecture, (v1_relat_1(k3_xboole_0(X1,esk1_0))), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 0.34/0.53  cnf(c_0_48, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.34/0.53  cnf(c_0_49, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_44, c_0_31])).
% 0.34/0.53  cnf(c_0_50, negated_conjecture, (r1_tarski(k1_relat_1(k3_xboole_0(esk2_0,X1)),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_45])).
% 0.34/0.53  cnf(c_0_51, negated_conjecture, (k2_xboole_0(k1_relat_1(k3_xboole_0(X1,esk1_0)),k1_relat_1(esk1_0))=k1_relat_1(esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_37])).
% 0.34/0.53  cnf(c_0_52, negated_conjecture, (~r1_tarski(k1_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.34/0.53  cnf(c_0_53, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_49])])).
% 0.34/0.53  cnf(c_0_54, negated_conjecture, (r1_tarski(k1_relat_1(k3_xboole_0(esk2_0,X1)),k3_xboole_0(X2,k1_relat_1(esk2_0)))|~r1_tarski(k1_relat_1(k3_xboole_0(esk2_0,X1)),X2)), inference(spm,[status(thm)],[c_0_38, c_0_50])).
% 0.34/0.53  cnf(c_0_55, negated_conjecture, (r1_tarski(k1_relat_1(k3_xboole_0(X1,esk1_0)),k1_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_23, c_0_51])).
% 0.34/0.53  cnf(c_0_56, negated_conjecture, (~r1_tarski(k1_relat_1(k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k1_relat_1(esk2_0),k1_relat_1(esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_53])).
% 0.34/0.53  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_53]), c_0_56]), ['proof']).
% 0.34/0.53  # SZS output end CNFRefutation
% 0.34/0.53  # Proof object total steps             : 58
% 0.34/0.53  # Proof object clause steps            : 37
% 0.34/0.53  # Proof object formula steps           : 21
% 0.34/0.53  # Proof object conjectures             : 17
% 0.34/0.53  # Proof object clause conjectures      : 14
% 0.34/0.53  # Proof object formula conjectures     : 3
% 0.34/0.53  # Proof object initial clauses used    : 13
% 0.34/0.53  # Proof object initial formulas used   : 10
% 0.34/0.53  # Proof object generating inferences   : 22
% 0.34/0.53  # Proof object simplifying inferences  : 10
% 0.34/0.53  # Training examples: 0 positive, 0 negative
% 0.34/0.53  # Parsed axioms                        : 15
% 0.34/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.34/0.53  # Initial clauses                      : 20
% 0.34/0.53  # Removed in clause preprocessing      : 0
% 0.34/0.53  # Initial clauses in saturation        : 20
% 0.34/0.53  # Processed clauses                    : 1722
% 0.34/0.53  # ...of these trivial                  : 200
% 0.34/0.53  # ...subsumed                          : 802
% 0.34/0.53  # ...remaining for further processing  : 720
% 0.34/0.53  # Other redundant clauses eliminated   : 2
% 0.34/0.53  # Clauses deleted for lack of memory   : 0
% 0.34/0.53  # Backward-subsumed                    : 21
% 0.34/0.53  # Backward-rewritten                   : 37
% 0.34/0.53  # Generated clauses                    : 13168
% 0.34/0.53  # ...of the previous two non-trivial   : 10045
% 0.34/0.53  # Contextual simplify-reflections      : 0
% 0.34/0.53  # Paramodulations                      : 13166
% 0.34/0.53  # Factorizations                       : 0
% 0.34/0.53  # Equation resolutions                 : 2
% 0.34/0.53  # Propositional unsat checks           : 0
% 0.34/0.53  #    Propositional check models        : 0
% 0.34/0.53  #    Propositional check unsatisfiable : 0
% 0.34/0.53  #    Propositional clauses             : 0
% 0.34/0.53  #    Propositional clauses after purity: 0
% 0.34/0.53  #    Propositional unsat core size     : 0
% 0.34/0.53  #    Propositional preprocessing time  : 0.000
% 0.34/0.53  #    Propositional encoding time       : 0.000
% 0.34/0.53  #    Propositional solver time         : 0.000
% 0.34/0.53  #    Success case prop preproc time    : 0.000
% 0.34/0.53  #    Success case prop encoding time   : 0.000
% 0.34/0.53  #    Success case prop solver time     : 0.000
% 0.34/0.53  # Current number of processed clauses  : 641
% 0.34/0.53  #    Positive orientable unit clauses  : 276
% 0.34/0.53  #    Positive unorientable unit clauses: 1
% 0.34/0.53  #    Negative unit clauses             : 1
% 0.34/0.53  #    Non-unit-clauses                  : 363
% 0.34/0.53  # Current number of unprocessed clauses: 8206
% 0.34/0.53  # ...number of literals in the above   : 9767
% 0.34/0.53  # Current number of archived formulas  : 0
% 0.34/0.53  # Current number of archived clauses   : 77
% 0.34/0.53  # Clause-clause subsumption calls (NU) : 13867
% 0.34/0.53  # Rec. Clause-clause subsumption calls : 13769
% 0.34/0.53  # Non-unit clause-clause subsumptions  : 823
% 0.34/0.53  # Unit Clause-clause subsumption calls : 800
% 0.34/0.53  # Rewrite failures with RHS unbound    : 0
% 0.34/0.53  # BW rewrite match attempts            : 714
% 0.34/0.53  # BW rewrite match successes           : 249
% 0.34/0.53  # Condensation attempts                : 0
% 0.34/0.53  # Condensation successes               : 0
% 0.34/0.53  # Termbank termtop insertions          : 151710
% 0.34/0.53  
% 0.34/0.53  # -------------------------------------------------
% 0.34/0.53  # User time                : 0.178 s
% 0.34/0.53  # System time              : 0.011 s
% 0.34/0.53  # Total time               : 0.189 s
% 0.34/0.53  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
