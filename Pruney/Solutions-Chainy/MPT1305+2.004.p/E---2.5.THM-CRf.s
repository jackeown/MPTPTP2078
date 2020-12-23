%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 143 expanded)
%              Number of clauses        :   26 (  51 expanded)
%              Number of leaves         :    5 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 694 expanded)
%              Number of equality atoms :   11 (  23 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d2_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t23_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( ( v2_tops_2(X2,X1)
                  & v2_tops_2(X3,X1) )
               => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tops_2)).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_7,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v2_tops_2(X21,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(X22,X21)
        | v4_pre_topc(X22,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk2_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))
        | v2_tops_2(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk2_2(X20,X21),X21)
        | v2_tops_2(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ l1_pre_topc(X20) )
      & ( ~ v4_pre_topc(esk2_2(X20,X21),X20)
        | v2_tops_2(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

fof(c_0_8,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | m1_subset_1(k4_subset_1(X14,X15,X16),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

fof(c_0_9,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k4_subset_1(X17,X18,X19) = k2_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( ( v2_tops_2(X2,X1)
                    & v2_tops_2(X3,X1) )
                 => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_tops_2])).

cnf(c_0_15,plain,
    ( v2_tops_2(k2_xboole_0(X1,X2),X3)
    | r2_hidden(esk2_2(X3,k2_xboole_0(X1,X2)),X2)
    | r2_hidden(esk2_2(X3,k2_xboole_0(X1,X2)),X1)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3)))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    & v2_tops_2(esk4_0,esk3_0)
    & v2_tops_2(esk5_0,esk3_0)
    & ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,esk5_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_18,plain,
    ( v2_tops_2(k2_xboole_0(X1,X2),X3)
    | r2_hidden(esk2_2(X3,k2_xboole_0(X1,X2)),X1)
    | r2_hidden(esk2_2(X3,k2_xboole_0(X1,X2)),X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3)))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,esk5_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( v2_tops_2(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v2_tops_2(k2_xboole_0(X1,esk5_0),esk3_0)
    | r2_hidden(esk2_2(esk3_0,k2_xboole_0(X1,esk5_0)),esk5_0)
    | r2_hidden(esk2_2(esk3_0,k2_xboole_0(X1,esk5_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_tops_2(k2_xboole_0(esk4_0,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_13]),c_0_19]),c_0_22])])).

cnf(c_0_27,negated_conjecture,
    ( v2_tops_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( v4_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_24]),c_0_20])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),esk4_0)
    | r2_hidden(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( v4_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_27]),c_0_20])])).

cnf(c_0_31,plain,
    ( v2_tops_2(X2,X1)
    | ~ v4_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( v4_pre_topc(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),esk3_0)
    | ~ m1_subset_1(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( ~ m1_subset_1(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_20])]),c_0_26])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_20])]),c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_16]),c_0_19]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:16:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.49  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.49  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.49  #
% 0.19/0.49  # Preprocessing time       : 0.029 s
% 0.19/0.49  # Presaturation interreduction done
% 0.19/0.49  
% 0.19/0.49  # Proof found!
% 0.19/0.49  # SZS status Theorem
% 0.19/0.49  # SZS output start CNFRefutation
% 0.19/0.49  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.49  fof(d2_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v4_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_2)).
% 0.19/0.49  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.19/0.49  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.19/0.49  fof(t23_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((v2_tops_2(X2,X1)&v2_tops_2(X3,X1))=>v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tops_2)).
% 0.19/0.49  fof(c_0_5, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.49  cnf(c_0_6, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.49  fof(c_0_7, plain, ![X20, X21, X22]:((~v2_tops_2(X21,X20)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(~r2_hidden(X22,X21)|v4_pre_topc(X22,X20)))|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~l1_pre_topc(X20))&((m1_subset_1(esk2_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))|v2_tops_2(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~l1_pre_topc(X20))&((r2_hidden(esk2_2(X20,X21),X21)|v2_tops_2(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~l1_pre_topc(X20))&(~v4_pre_topc(esk2_2(X20,X21),X20)|v2_tops_2(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~l1_pre_topc(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).
% 0.19/0.49  fof(c_0_8, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|~m1_subset_1(X16,k1_zfmisc_1(X14))|m1_subset_1(k4_subset_1(X14,X15,X16),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.19/0.49  fof(c_0_9, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|~m1_subset_1(X19,k1_zfmisc_1(X17))|k4_subset_1(X17,X18,X19)=k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.19/0.49  cnf(c_0_10, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_6])).
% 0.19/0.49  cnf(c_0_11, plain, (r2_hidden(esk2_2(X1,X2),X2)|v2_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.49  cnf(c_0_12, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.49  cnf(c_0_13, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.49  fof(c_0_14, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((v2_tops_2(X2,X1)&v2_tops_2(X3,X1))=>v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t23_tops_2])).
% 0.19/0.49  cnf(c_0_15, plain, (v2_tops_2(k2_xboole_0(X1,X2),X3)|r2_hidden(esk2_2(X3,k2_xboole_0(X1,X2)),X2)|r2_hidden(esk2_2(X3,k2_xboole_0(X1,X2)),X1)|~l1_pre_topc(X3)|~m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.49  cnf(c_0_16, plain, (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.49  fof(c_0_17, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))&(m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))&((v2_tops_2(esk4_0,esk3_0)&v2_tops_2(esk5_0,esk3_0))&~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,esk5_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.49  cnf(c_0_18, plain, (v2_tops_2(k2_xboole_0(X1,X2),X3)|r2_hidden(esk2_2(X3,k2_xboole_0(X1,X2)),X1)|r2_hidden(esk2_2(X3,k2_xboole_0(X1,X2)),X2)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.49  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.49  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.49  cnf(c_0_21, negated_conjecture, (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,esk5_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.49  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.49  cnf(c_0_23, plain, (v4_pre_topc(X3,X2)|~v2_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.49  cnf(c_0_24, negated_conjecture, (v2_tops_2(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.49  cnf(c_0_25, negated_conjecture, (v2_tops_2(k2_xboole_0(X1,esk5_0),esk3_0)|r2_hidden(esk2_2(esk3_0,k2_xboole_0(X1,esk5_0)),esk5_0)|r2_hidden(esk2_2(esk3_0,k2_xboole_0(X1,esk5_0)),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.19/0.49  cnf(c_0_26, negated_conjecture, (~v2_tops_2(k2_xboole_0(esk4_0,esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_13]), c_0_19]), c_0_22])])).
% 0.19/0.49  cnf(c_0_27, negated_conjecture, (v2_tops_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.49  cnf(c_0_28, negated_conjecture, (v4_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_24]), c_0_20])])).
% 0.19/0.49  cnf(c_0_29, negated_conjecture, (r2_hidden(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),esk4_0)|r2_hidden(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_22]), c_0_26])).
% 0.19/0.49  cnf(c_0_30, negated_conjecture, (v4_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_22]), c_0_27]), c_0_20])])).
% 0.19/0.49  cnf(c_0_31, plain, (v2_tops_2(X2,X1)|~v4_pre_topc(esk2_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.49  cnf(c_0_32, negated_conjecture, (v4_pre_topc(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),esk3_0)|~m1_subset_1(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.19/0.49  cnf(c_0_33, negated_conjecture, (~m1_subset_1(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_20])]), c_0_26])).
% 0.19/0.49  cnf(c_0_34, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.49  cnf(c_0_35, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_20])]), c_0_26])).
% 0.19/0.49  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_16]), c_0_19]), c_0_22])]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 37
% 0.19/0.49  # Proof object clause steps            : 26
% 0.19/0.49  # Proof object formula steps           : 11
% 0.19/0.49  # Proof object conjectures             : 18
% 0.19/0.49  # Proof object clause conjectures      : 15
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 13
% 0.19/0.49  # Proof object initial formulas used   : 5
% 0.19/0.49  # Proof object generating inferences   : 13
% 0.19/0.49  # Proof object simplifying inferences  : 22
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 5
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 18
% 0.19/0.49  # Removed in clause preprocessing      : 0
% 0.19/0.49  # Initial clauses in saturation        : 18
% 0.19/0.49  # Processed clauses                    : 1473
% 0.19/0.49  # ...of these trivial                  : 26
% 0.19/0.49  # ...subsumed                          : 1168
% 0.19/0.49  # ...remaining for further processing  : 279
% 0.19/0.49  # Other redundant clauses eliminated   : 3
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 4
% 0.19/0.49  # Backward-rewritten                   : 4
% 0.19/0.49  # Generated clauses                    : 5607
% 0.19/0.49  # ...of the previous two non-trivial   : 5149
% 0.19/0.49  # Contextual simplify-reflections      : 8
% 0.19/0.49  # Paramodulations                      : 5511
% 0.19/0.49  # Factorizations                       : 64
% 0.19/0.49  # Equation resolutions                 : 32
% 0.19/0.49  # Propositional unsat checks           : 0
% 0.19/0.49  #    Propositional check models        : 0
% 0.19/0.49  #    Propositional check unsatisfiable : 0
% 0.19/0.49  #    Propositional clauses             : 0
% 0.19/0.49  #    Propositional clauses after purity: 0
% 0.19/0.49  #    Propositional unsat core size     : 0
% 0.19/0.49  #    Propositional preprocessing time  : 0.000
% 0.19/0.49  #    Propositional encoding time       : 0.000
% 0.19/0.49  #    Propositional solver time         : 0.000
% 0.19/0.49  #    Success case prop preproc time    : 0.000
% 0.19/0.49  #    Success case prop encoding time   : 0.000
% 0.19/0.49  #    Success case prop solver time     : 0.000
% 0.19/0.49  # Current number of processed clauses  : 253
% 0.19/0.49  #    Positive orientable unit clauses  : 18
% 0.19/0.49  #    Positive unorientable unit clauses: 0
% 0.19/0.49  #    Negative unit clauses             : 3
% 0.19/0.49  #    Non-unit-clauses                  : 232
% 0.19/0.49  # Current number of unprocessed clauses: 3667
% 0.19/0.49  # ...number of literals in the above   : 13672
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 26
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 36973
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 7884
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 1178
% 0.19/0.49  # Unit Clause-clause subsumption calls : 208
% 0.19/0.49  # Rewrite failures with RHS unbound    : 0
% 0.19/0.49  # BW rewrite match attempts            : 37
% 0.19/0.49  # BW rewrite match successes           : 3
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 104206
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.144 s
% 0.19/0.49  # System time              : 0.005 s
% 0.19/0.49  # Total time               : 0.149 s
% 0.19/0.49  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
