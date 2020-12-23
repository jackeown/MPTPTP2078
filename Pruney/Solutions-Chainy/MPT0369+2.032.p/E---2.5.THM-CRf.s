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
% DateTime   : Thu Dec  3 10:46:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 462 expanded)
%              Number of clauses        :   33 ( 200 expanded)
%              Number of leaves         :    9 ( 120 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 ( 971 expanded)
%              Number of equality atoms :   27 ( 380 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_subset_1,conjecture,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ( ~ r2_hidden(X3,X2)
               => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( X1 != k1_xboole_0
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X1))
           => ! [X3] :
                ( m1_subset_1(X3,X1)
               => ( ~ r2_hidden(X3,X2)
                 => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_subset_1])).

fof(c_0_10,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X13,X12)
        | r2_hidden(X13,X12)
        | v1_xboole_0(X12) )
      & ( ~ r2_hidden(X13,X12)
        | m1_subset_1(X13,X12)
        | v1_xboole_0(X12) )
      & ( ~ m1_subset_1(X13,X12)
        | v1_xboole_0(X13)
        | ~ v1_xboole_0(X12) )
      & ( ~ v1_xboole_0(X13)
        | m1_subset_1(X13,X12)
        | ~ v1_xboole_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_11,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,esk1_0)
    & ~ r2_hidden(esk3_0,esk2_0)
    & ~ r2_hidden(esk3_0,k3_subset_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r2_hidden(X5,X6)
        | ~ r2_hidden(X5,X7)
        | ~ r2_hidden(X5,k5_xboole_0(X6,X7)) )
      & ( r2_hidden(X5,X6)
        | r2_hidden(X5,X7)
        | ~ r2_hidden(X5,k5_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X5,X6)
        | r2_hidden(X5,X7)
        | r2_hidden(X5,k5_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X5,X7)
        | r2_hidden(X5,X6)
        | r2_hidden(X5,k5_xboole_0(X6,X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0)
    | v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | k3_subset_1(X14,X15) = k4_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_0,k5_xboole_0(esk1_0,X1))
    | r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_29,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk3_0,k5_xboole_0(X2,k5_xboole_0(esk1_0,X1)))
    | ~ r2_hidden(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_28])).

cnf(c_0_32,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk3_0,k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) = k3_subset_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k3_subset_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_38,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | k3_subset_1(X18,k3_subset_1(X18,X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_39,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | m1_subset_1(k3_subset_1(X16,X17),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1)))
    | ~ r2_hidden(esk3_0,k3_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_36]),c_0_37])).

cnf(c_0_42,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2)
    | ~ m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_36]),c_0_46]),c_0_47])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_49]),c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.20/0.40  # and selection function HSelectMinInfpos.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.027 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t50_subset_1, conjecture, ![X1]:(X1!=k1_xboole_0=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,X1)=>(~(r2_hidden(X3,X2))=>r2_hidden(X3,k3_subset_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 0.20/0.40  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.40  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.40  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.20/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.40  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.40  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.40  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.20/0.40  fof(c_0_9, negated_conjecture, ~(![X1]:(X1!=k1_xboole_0=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,X1)=>(~(r2_hidden(X3,X2))=>r2_hidden(X3,k3_subset_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t50_subset_1])).
% 0.20/0.40  fof(c_0_10, plain, ![X12, X13]:(((~m1_subset_1(X13,X12)|r2_hidden(X13,X12)|v1_xboole_0(X12))&(~r2_hidden(X13,X12)|m1_subset_1(X13,X12)|v1_xboole_0(X12)))&((~m1_subset_1(X13,X12)|v1_xboole_0(X13)|~v1_xboole_0(X12))&(~v1_xboole_0(X13)|m1_subset_1(X13,X12)|~v1_xboole_0(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.40  fof(c_0_11, negated_conjecture, (esk1_0!=k1_xboole_0&(m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk3_0,esk1_0)&(~r2_hidden(esk3_0,esk2_0)&~r2_hidden(esk3_0,k3_subset_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.20/0.40  fof(c_0_12, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.40  cnf(c_0_13, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  fof(c_0_15, plain, ![X5, X6, X7]:(((~r2_hidden(X5,X6)|~r2_hidden(X5,X7)|~r2_hidden(X5,k5_xboole_0(X6,X7)))&(r2_hidden(X5,X6)|r2_hidden(X5,X7)|~r2_hidden(X5,k5_xboole_0(X6,X7))))&((~r2_hidden(X5,X6)|r2_hidden(X5,X7)|r2_hidden(X5,k5_xboole_0(X6,X7)))&(~r2_hidden(X5,X7)|r2_hidden(X5,X6)|r2_hidden(X5,k5_xboole_0(X6,X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.20/0.40  cnf(c_0_16, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_17, negated_conjecture, (r2_hidden(esk3_0,esk1_0)|v1_xboole_0(esk1_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.40  cnf(c_0_18, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  fof(c_0_19, plain, ![X10, X11]:k4_xboole_0(X10,k4_xboole_0(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.40  fof(c_0_20, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.40  cnf(c_0_21, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (r2_hidden(esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.20/0.40  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  fof(c_0_25, plain, ![X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|k3_subset_1(X14,X15)=k4_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.40  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_27, negated_conjecture, (r2_hidden(esk3_0,k5_xboole_0(esk1_0,X1))|r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.40  cnf(c_0_28, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 0.20/0.40  cnf(c_0_29, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_30, negated_conjecture, (r2_hidden(esk3_0,X1)|~r2_hidden(esk3_0,k5_xboole_0(X2,k5_xboole_0(esk1_0,X1)))|~r2_hidden(esk3_0,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.40  cnf(c_0_31, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_28, c_0_28])).
% 0.20/0.40  cnf(c_0_32, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_29, c_0_24])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_0,X1)|~r2_hidden(esk3_0,k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,X1)))), inference(spm,[status(thm)],[c_0_30, c_0_22])).
% 0.20/0.40  cnf(c_0_35, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_31])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))=k3_subset_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk3_0,k3_subset_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  fof(c_0_38, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|k3_subset_1(X18,k3_subset_1(X18,X19))=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.40  fof(c_0_39, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|m1_subset_1(k3_subset_1(X16,X17),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (r2_hidden(esk3_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1)))|~r2_hidden(esk3_0,k3_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (r2_hidden(esk3_0,k3_xboole_0(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_36]), c_0_37])).
% 0.20/0.40  cnf(c_0_42, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.40  cnf(c_0_43, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(esk3_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.40  cnf(c_0_45, plain, (k3_subset_1(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)|~m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_31]), c_0_35])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_42, c_0_33])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (m1_subset_1(k3_subset_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_43, c_0_33])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (r2_hidden(esk3_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))), inference(spm,[status(thm)],[c_0_40, c_0_44])).
% 0.20/0.40  cnf(c_0_49, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_36]), c_0_46]), c_0_47])])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (~r2_hidden(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_49]), c_0_49]), c_0_50]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 52
% 0.20/0.40  # Proof object clause steps            : 33
% 0.20/0.40  # Proof object formula steps           : 19
% 0.20/0.40  # Proof object conjectures             : 22
% 0.20/0.40  # Proof object clause conjectures      : 19
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 14
% 0.20/0.40  # Proof object initial formulas used   : 9
% 0.20/0.40  # Proof object generating inferences   : 15
% 0.20/0.40  # Proof object simplifying inferences  : 14
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 9
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 19
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 18
% 0.20/0.40  # Processed clauses                    : 359
% 0.20/0.40  # ...of these trivial                  : 4
% 0.20/0.40  # ...subsumed                          : 160
% 0.20/0.40  # ...remaining for further processing  : 195
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 50
% 0.20/0.40  # Generated clauses                    : 859
% 0.20/0.40  # ...of the previous two non-trivial   : 750
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 853
% 0.20/0.40  # Factorizations                       : 6
% 0.20/0.40  # Equation resolutions                 : 0
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 127
% 0.20/0.40  #    Positive orientable unit clauses  : 12
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 9
% 0.20/0.40  #    Non-unit-clauses                  : 106
% 0.20/0.40  # Current number of unprocessed clauses: 406
% 0.20/0.40  # ...number of literals in the above   : 1155
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 69
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 2254
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 1825
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 158
% 0.20/0.40  # Unit Clause-clause subsumption calls : 1160
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 15
% 0.20/0.40  # BW rewrite match successes           : 4
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 14968
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.051 s
% 0.20/0.40  # System time              : 0.002 s
% 0.20/0.40  # Total time               : 0.053 s
% 0.20/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
