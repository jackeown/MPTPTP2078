%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 180 expanded)
%              Number of clauses        :   38 (  80 expanded)
%              Number of leaves         :   15 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  150 ( 451 expanded)
%              Number of equality atoms :   19 (  65 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t40_subset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X2,k3_subset_1(X1,X3)) )
       => X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t38_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(c_0_15,plain,(
    ! [X23] : m1_subset_1(k2_subset_1(X23),k1_zfmisc_1(X23)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_16,plain,(
    ! [X21] : k2_subset_1(X21) = X21 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_17,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X19,X18)
        | r2_hidden(X19,X18)
        | v1_xboole_0(X18) )
      & ( ~ r2_hidden(X19,X18)
        | m1_subset_1(X19,X18)
        | v1_xboole_0(X18) )
      & ( ~ m1_subset_1(X19,X18)
        | v1_xboole_0(X19)
        | ~ v1_xboole_0(X18) )
      & ( ~ v1_xboole_0(X19)
        | m1_subset_1(X19,X18)
        | ~ v1_xboole_0(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X24] : ~ v1_xboole_0(k1_zfmisc_1(X24)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X1))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X2,k3_subset_1(X1,X3)) )
         => X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t40_subset_1])).

fof(c_0_22,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | r1_tarski(k1_zfmisc_1(X16),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))
    & esk3_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_28,plain,(
    ! [X26,X27,X28] :
      ( ( ~ r1_tarski(X27,X28)
        | r1_tarski(k3_subset_1(X26,X28),k3_subset_1(X26,X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26)) )
      & ( ~ r1_tarski(k3_subset_1(X26,X28),k3_subset_1(X26,X27))
        | r1_tarski(X27,X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

fof(c_0_29,plain,(
    ! [X22] : m1_subset_1(k1_subset_1(X22),k1_zfmisc_1(X22)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_30,plain,(
    ! [X20] : k1_subset_1(X20) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_31,plain,(
    ! [X25] : k2_subset_1(X25) = k3_subset_1(X25,k1_subset_1(X25)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_subset_1(X3,X2),k3_subset_1(X3,X1))
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(k3_subset_1(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_19]),c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,X15)
      | ~ v1_xboole_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(k3_subset_1(esk2_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(k3_subset_1(esk2_0,esk4_0)),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_50])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_57,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_60,plain,(
    ! [X29,X30] :
      ( ( ~ r1_tarski(X30,k3_subset_1(X29,X30))
        | X30 = k1_subset_1(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(X29)) )
      & ( X30 != k1_subset_1(X29)
        | r1_tarski(X30,k3_subset_1(X29,X30))
        | ~ m1_subset_1(X30,k1_zfmisc_1(X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_58]),c_0_59])])).

cnf(c_0_63,plain,
    ( X1 = k1_subset_1(X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk2_0,esk3_0))
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_39])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_35])).

cnf(c_0_67,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_58])]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.20/0.38  # and selection function SelectLargestOrientable.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.020 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.38  fof(t40_subset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.20/0.38  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 0.20/0.38  fof(dt_k1_subset_1, axiom, ![X1]:m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 0.20/0.38  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.20/0.38  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 0.20/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.38  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 0.20/0.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.38  fof(t38_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 0.20/0.38  fof(c_0_15, plain, ![X23]:m1_subset_1(k2_subset_1(X23),k1_zfmisc_1(X23)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.38  fof(c_0_16, plain, ![X21]:k2_subset_1(X21)=X21, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.38  fof(c_0_17, plain, ![X18, X19]:(((~m1_subset_1(X19,X18)|r2_hidden(X19,X18)|v1_xboole_0(X18))&(~r2_hidden(X19,X18)|m1_subset_1(X19,X18)|v1_xboole_0(X18)))&((~m1_subset_1(X19,X18)|v1_xboole_0(X19)|~v1_xboole_0(X18))&(~v1_xboole_0(X19)|m1_subset_1(X19,X18)|~v1_xboole_0(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.38  cnf(c_0_18, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_19, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  fof(c_0_20, plain, ![X24]:~v1_xboole_0(k1_zfmisc_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.38  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t40_subset_1])).
% 0.20/0.38  fof(c_0_22, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.38  cnf(c_0_25, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  fof(c_0_26, plain, ![X16, X17]:(~r1_tarski(X16,X17)|r1_tarski(k1_zfmisc_1(X16),k1_zfmisc_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.20/0.38  fof(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0)))&esk3_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.38  fof(c_0_28, plain, ![X26, X27, X28]:((~r1_tarski(X27,X28)|r1_tarski(k3_subset_1(X26,X28),k3_subset_1(X26,X27))|~m1_subset_1(X28,k1_zfmisc_1(X26))|~m1_subset_1(X27,k1_zfmisc_1(X26)))&(~r1_tarski(k3_subset_1(X26,X28),k3_subset_1(X26,X27))|r1_tarski(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(X26))|~m1_subset_1(X27,k1_zfmisc_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 0.20/0.38  fof(c_0_29, plain, ![X22]:m1_subset_1(k1_subset_1(X22),k1_zfmisc_1(X22)), inference(variable_rename,[status(thm)],[dt_k1_subset_1])).
% 0.20/0.38  fof(c_0_30, plain, ![X20]:k1_subset_1(X20)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.20/0.38  fof(c_0_31, plain, ![X25]:k2_subset_1(X25)=k3_subset_1(X25,k1_subset_1(X25)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.20/0.38  cnf(c_0_32, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_33, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.20/0.38  cnf(c_0_34, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_36, plain, (r1_tarski(k3_subset_1(X3,X2),k3_subset_1(X3,X1))|~r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_38, plain, (m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_39, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.38  cnf(c_0_40, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  fof(c_0_41, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.38  cnf(c_0_42, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(k3_subset_1(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.38  cnf(c_0_45, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.38  cnf(c_0_46, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_19]), c_0_39])).
% 0.20/0.38  cnf(c_0_47, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.38  fof(c_0_48, plain, ![X14, X15]:(~r2_hidden(X14,X15)|~v1_xboole_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])])).
% 0.20/0.38  cnf(c_0_51, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_52, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_0,X1)|~r1_tarski(k1_zfmisc_1(k3_subset_1(esk2_0,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_32, c_0_49])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (r1_tarski(k1_zfmisc_1(k3_subset_1(esk2_0,esk4_0)),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_50])).
% 0.20/0.38  cnf(c_0_55, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.38  fof(c_0_57, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X11,X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  fof(c_0_60, plain, ![X29, X30]:((~r1_tarski(X30,k3_subset_1(X29,X30))|X30=k1_subset_1(X29)|~m1_subset_1(X30,k1_zfmisc_1(X29)))&(X30!=k1_subset_1(X29)|r1_tarski(X30,k3_subset_1(X29,X30))|~m1_subset_1(X30,k1_zfmisc_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).
% 0.20/0.38  cnf(c_0_61, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_58]), c_0_59])])).
% 0.20/0.38  cnf(c_0_63, plain, (X1=k1_subset_1(X2)|~r1_tarski(X1,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk2_0,esk3_0))|~r1_tarski(X1,k3_subset_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.38  cnf(c_0_65, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X1))), inference(rw,[status(thm)],[c_0_63, c_0_39])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_64, c_0_35])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_58])]), c_0_67]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 69
% 0.20/0.38  # Proof object clause steps            : 38
% 0.20/0.38  # Proof object formula steps           : 31
% 0.20/0.38  # Proof object conjectures             : 19
% 0.20/0.38  # Proof object clause conjectures      : 16
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 19
% 0.20/0.38  # Proof object initial formulas used   : 15
% 0.20/0.38  # Proof object generating inferences   : 14
% 0.20/0.38  # Proof object simplifying inferences  : 15
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 15
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 25
% 0.20/0.39  # Removed in clause preprocessing      : 2
% 0.20/0.39  # Initial clauses in saturation        : 23
% 0.20/0.39  # Processed clauses                    : 330
% 0.20/0.39  # ...of these trivial                  : 3
% 0.20/0.39  # ...subsumed                          : 62
% 0.20/0.39  # ...remaining for further processing  : 265
% 0.20/0.39  # Other redundant clauses eliminated   : 1
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 2
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 969
% 0.20/0.39  # ...of the previous two non-trivial   : 560
% 0.20/0.39  # Contextual simplify-reflections      : 1
% 0.20/0.39  # Paramodulations                      : 968
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 1
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 240
% 0.20/0.39  #    Positive orientable unit clauses  : 130
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 108
% 0.20/0.39  # Current number of unprocessed clauses: 272
% 0.20/0.39  # ...number of literals in the above   : 511
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 26
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 908
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 859
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 8
% 0.20/0.39  # Unit Clause-clause subsumption calls : 39
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 625
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 16687
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.039 s
% 0.20/0.39  # System time              : 0.007 s
% 0.20/0.39  # Total time               : 0.046 s
% 0.20/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
