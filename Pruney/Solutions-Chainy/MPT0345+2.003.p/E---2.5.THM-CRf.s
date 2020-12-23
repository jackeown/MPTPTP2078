%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:11 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 358 expanded)
%              Number of clauses        :   30 ( 140 expanded)
%              Number of leaves         :    6 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  159 (2104 expanded)
%              Number of equality atoms :   21 ( 245 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(X1))
             => ( ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(X5,X2)
                    <=> ( r2_hidden(X5,X3)
                        | r2_hidden(X5,X4) ) ) )
               => X2 = k4_subset_1(X1,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,X2)
                      <=> ( r2_hidden(X5,X3)
                          | r2_hidden(X5,X4) ) ) )
                 => X2 = k4_subset_1(X1,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t15_subset_1])).

fof(c_0_7,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ r2_hidden(X23,X22)
      | r2_hidden(X23,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_8,negated_conjecture,(
    ! [X31] :
      ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
      & ( ~ r2_hidden(X31,esk4_0)
        | r2_hidden(X31,esk5_0)
        | r2_hidden(X31,esk6_0)
        | ~ m1_subset_1(X31,esk3_0) )
      & ( ~ r2_hidden(X31,esk5_0)
        | r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,esk3_0) )
      & ( ~ r2_hidden(X31,esk6_0)
        | r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,esk3_0) )
      & esk4_0 != k4_subset_1(esk3_0,esk5_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X20,X19)
        | r2_hidden(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ r2_hidden(X20,X19)
        | m1_subset_1(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ m1_subset_1(X20,X19)
        | v1_xboole_0(X20)
        | ~ v1_xboole_0(X19) )
      & ( ~ v1_xboole_0(X20)
        | m1_subset_1(X20,X19)
        | ~ v1_xboole_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_10,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X13,X12)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | r2_hidden(X14,X12)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X15)
        | ~ r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X16)
        | ~ r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k2_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X17)
        | r2_hidden(esk2_3(X15,X16,X17),X15)
        | r2_hidden(esk2_3(X15,X16,X17),X16)
        | X17 = k2_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | ~ m1_subset_1(X26,k1_zfmisc_1(X24))
      | k4_subset_1(X24,X25,X26) = k2_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( X1 = k2_xboole_0(X2,esk6_0)
    | r2_hidden(esk2_3(X2,esk6_0,X1),esk3_0)
    | r2_hidden(esk2_3(X2,esk6_0,X1),X2)
    | r2_hidden(esk2_3(X2,esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( esk4_0 != k4_subset_1(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k2_xboole_0(X1,esk6_0) = esk4_0
    | r2_hidden(esk2_3(X1,esk6_0,esk4_0),esk3_0)
    | r2_hidden(esk2_3(X1,esk6_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_12]),c_0_22])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k2_xboole_0(esk5_0,X2)
    | r2_hidden(esk2_3(esk5_0,X2,X1),esk4_0)
    | r2_hidden(esk2_3(esk5_0,X2,X1),X2)
    | r2_hidden(esk2_3(esk5_0,X2,X1),X1)
    | ~ r2_hidden(esk2_3(esk5_0,X2,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_21]),c_0_17])).

cnf(c_0_35,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_30]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_36]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_36])]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:24:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.36/0.53  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.36/0.53  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.36/0.53  #
% 0.36/0.53  # Preprocessing time       : 0.027 s
% 0.36/0.53  # Presaturation interreduction done
% 0.36/0.53  
% 0.36/0.53  # Proof found!
% 0.36/0.53  # SZS status Theorem
% 0.36/0.53  # SZS output start CNFRefutation
% 0.36/0.53  fof(t15_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,X2)<=>(r2_hidden(X5,X3)|r2_hidden(X5,X4))))=>X2=k4_subset_1(X1,X3,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_subset_1)).
% 0.36/0.53  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.36/0.53  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.36/0.53  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.36/0.53  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.36/0.53  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.36/0.53  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,X2)<=>(r2_hidden(X5,X3)|r2_hidden(X5,X4))))=>X2=k4_subset_1(X1,X3,X4)))))), inference(assume_negation,[status(cth)],[t15_subset_1])).
% 0.36/0.53  fof(c_0_7, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|(~r2_hidden(X23,X22)|r2_hidden(X23,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.36/0.53  fof(c_0_8, negated_conjecture, ![X31]:(m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))&(((~r2_hidden(X31,esk4_0)|(r2_hidden(X31,esk5_0)|r2_hidden(X31,esk6_0))|~m1_subset_1(X31,esk3_0))&((~r2_hidden(X31,esk5_0)|r2_hidden(X31,esk4_0)|~m1_subset_1(X31,esk3_0))&(~r2_hidden(X31,esk6_0)|r2_hidden(X31,esk4_0)|~m1_subset_1(X31,esk3_0))))&esk4_0!=k4_subset_1(esk3_0,esk5_0,esk6_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.36/0.53  fof(c_0_9, plain, ![X19, X20]:(((~m1_subset_1(X20,X19)|r2_hidden(X20,X19)|v1_xboole_0(X19))&(~r2_hidden(X20,X19)|m1_subset_1(X20,X19)|v1_xboole_0(X19)))&((~m1_subset_1(X20,X19)|v1_xboole_0(X20)|~v1_xboole_0(X19))&(~v1_xboole_0(X20)|m1_subset_1(X20,X19)|~v1_xboole_0(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.36/0.53  fof(c_0_10, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.36/0.53  cnf(c_0_11, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.36/0.53  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.36/0.53  fof(c_0_13, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X13,X12)|(r2_hidden(X13,X10)|r2_hidden(X13,X11))|X12!=k2_xboole_0(X10,X11))&((~r2_hidden(X14,X10)|r2_hidden(X14,X12)|X12!=k2_xboole_0(X10,X11))&(~r2_hidden(X14,X11)|r2_hidden(X14,X12)|X12!=k2_xboole_0(X10,X11))))&(((~r2_hidden(esk2_3(X15,X16,X17),X15)|~r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k2_xboole_0(X15,X16))&(~r2_hidden(esk2_3(X15,X16,X17),X16)|~r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k2_xboole_0(X15,X16)))&(r2_hidden(esk2_3(X15,X16,X17),X17)|(r2_hidden(esk2_3(X15,X16,X17),X15)|r2_hidden(esk2_3(X15,X16,X17),X16))|X17=k2_xboole_0(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.36/0.53  cnf(c_0_14, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.36/0.53  cnf(c_0_15, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.36/0.53  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.36/0.53  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.36/0.53  cnf(c_0_18, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.36/0.53  fof(c_0_19, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|~m1_subset_1(X26,k1_zfmisc_1(X24))|k4_subset_1(X24,X25,X26)=k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.36/0.53  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.36/0.53  cnf(c_0_21, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_14, c_0_15])).
% 0.36/0.53  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.36/0.53  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_11, c_0_16])).
% 0.36/0.53  cnf(c_0_24, negated_conjecture, (X1=k2_xboole_0(X2,esk6_0)|r2_hidden(esk2_3(X2,esk6_0,X1),esk3_0)|r2_hidden(esk2_3(X2,esk6_0,X1),X2)|r2_hidden(esk2_3(X2,esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.36/0.53  cnf(c_0_25, negated_conjecture, (esk4_0!=k4_subset_1(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.36/0.53  cnf(c_0_26, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.36/0.53  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.36/0.53  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_11, c_0_22])).
% 0.36/0.53  cnf(c_0_29, negated_conjecture, (k2_xboole_0(X1,esk6_0)=esk4_0|r2_hidden(esk2_3(X1,esk6_0,esk4_0),esk3_0)|r2_hidden(esk2_3(X1,esk6_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.36/0.53  cnf(c_0_30, negated_conjecture, (k2_xboole_0(esk5_0,esk6_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_12]), c_0_22])])).
% 0.36/0.53  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.36/0.53  cnf(c_0_32, negated_conjecture, (X1=k2_xboole_0(esk5_0,X2)|r2_hidden(esk2_3(esk5_0,X2,X1),esk4_0)|r2_hidden(esk2_3(esk5_0,X2,X1),X2)|r2_hidden(esk2_3(esk5_0,X2,X1),X1)|~r2_hidden(esk2_3(esk5_0,X2,X1),esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_18])).
% 0.36/0.53  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.36/0.53  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_21]), c_0_17])).
% 0.36/0.53  cnf(c_0_35, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.36/0.53  cnf(c_0_36, negated_conjecture, (r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_30]), c_0_34])).
% 0.36/0.53  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk5_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.36/0.53  cnf(c_0_38, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.36/0.53  cnf(c_0_39, negated_conjecture, (~r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_30])).
% 0.36/0.53  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,esk6_0)|r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_23])).
% 0.36/0.53  cnf(c_0_41, negated_conjecture, (~r2_hidden(esk2_3(esk5_0,esk6_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_36]), c_0_30])).
% 0.36/0.53  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_36])]), c_0_41]), ['proof']).
% 0.36/0.53  # SZS output end CNFRefutation
% 0.36/0.53  # Proof object total steps             : 43
% 0.36/0.53  # Proof object clause steps            : 30
% 0.36/0.53  # Proof object formula steps           : 13
% 0.36/0.53  # Proof object conjectures             : 25
% 0.36/0.53  # Proof object clause conjectures      : 22
% 0.36/0.53  # Proof object formula conjectures     : 3
% 0.36/0.53  # Proof object initial clauses used    : 14
% 0.36/0.53  # Proof object initial formulas used   : 6
% 0.36/0.53  # Proof object generating inferences   : 15
% 0.36/0.53  # Proof object simplifying inferences  : 14
% 0.36/0.53  # Training examples: 0 positive, 0 negative
% 0.36/0.53  # Parsed axioms                        : 6
% 0.36/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.36/0.53  # Initial clauses                      : 21
% 0.36/0.53  # Removed in clause preprocessing      : 0
% 0.36/0.53  # Initial clauses in saturation        : 21
% 0.36/0.53  # Processed clauses                    : 2021
% 0.36/0.53  # ...of these trivial                  : 58
% 0.36/0.53  # ...subsumed                          : 1419
% 0.36/0.53  # ...remaining for further processing  : 544
% 0.36/0.53  # Other redundant clauses eliminated   : 27
% 0.36/0.53  # Clauses deleted for lack of memory   : 0
% 0.36/0.53  # Backward-subsumed                    : 51
% 0.36/0.53  # Backward-rewritten                   : 7
% 0.36/0.53  # Generated clauses                    : 9252
% 0.36/0.53  # ...of the previous two non-trivial   : 8886
% 0.36/0.53  # Contextual simplify-reflections      : 52
% 0.36/0.53  # Paramodulations                      : 8945
% 0.36/0.53  # Factorizations                       : 270
% 0.36/0.53  # Equation resolutions                 : 31
% 0.36/0.53  # Propositional unsat checks           : 0
% 0.36/0.53  #    Propositional check models        : 0
% 0.36/0.53  #    Propositional check unsatisfiable : 0
% 0.36/0.53  #    Propositional clauses             : 0
% 0.36/0.53  #    Propositional clauses after purity: 0
% 0.36/0.53  #    Propositional unsat core size     : 0
% 0.36/0.53  #    Propositional preprocessing time  : 0.000
% 0.36/0.53  #    Propositional encoding time       : 0.000
% 0.36/0.53  #    Propositional solver time         : 0.000
% 0.36/0.53  #    Success case prop preproc time    : 0.000
% 0.36/0.53  #    Success case prop encoding time   : 0.000
% 0.36/0.53  #    Success case prop solver time     : 0.000
% 0.36/0.53  # Current number of processed clauses  : 459
% 0.36/0.53  #    Positive orientable unit clauses  : 18
% 0.36/0.53  #    Positive unorientable unit clauses: 0
% 0.36/0.53  #    Negative unit clauses             : 8
% 0.36/0.53  #    Non-unit-clauses                  : 433
% 0.36/0.53  # Current number of unprocessed clauses: 6738
% 0.36/0.53  # ...number of literals in the above   : 35717
% 0.36/0.53  # Current number of archived formulas  : 0
% 0.36/0.53  # Current number of archived clauses   : 85
% 0.36/0.53  # Clause-clause subsumption calls (NU) : 26075
% 0.36/0.53  # Rec. Clause-clause subsumption calls : 11159
% 0.36/0.53  # Non-unit clause-clause subsumptions  : 717
% 0.36/0.53  # Unit Clause-clause subsumption calls : 485
% 0.36/0.53  # Rewrite failures with RHS unbound    : 0
% 0.36/0.53  # BW rewrite match attempts            : 10
% 0.36/0.53  # BW rewrite match successes           : 6
% 0.36/0.53  # Condensation attempts                : 0
% 0.36/0.53  # Condensation successes               : 0
% 0.36/0.53  # Termbank termtop insertions          : 161849
% 0.36/0.53  
% 0.36/0.53  # -------------------------------------------------
% 0.36/0.53  # User time                : 0.183 s
% 0.36/0.53  # System time              : 0.011 s
% 0.36/0.53  # Total time               : 0.195 s
% 0.36/0.53  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
