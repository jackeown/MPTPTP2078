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
% DateTime   : Thu Dec  3 11:14:47 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   53 (  81 expanded)
%              Number of clauses        :   30 (  35 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  148 ( 257 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t35_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => m2_connsp_2(k2_struct_0(X1),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

fof(d2_connsp_2,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m2_connsp_2(X3,X1,X2)
              <=> r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(t43_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k1_tops_1(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_11,plain,(
    ! [X18] : m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_12,plain,(
    ! [X17] : k2_subset_1(X17) = X17 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_13,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | r1_tarski(X12,X10)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r1_tarski(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | ~ r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_14,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => m2_connsp_2(k2_struct_0(X1),X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t35_connsp_2])).

fof(c_0_16,plain,(
    ! [X27,X28,X29] :
      ( ( ~ m2_connsp_2(X29,X27,X28)
        | r1_tarski(X28,k1_tops_1(X27,X29))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r1_tarski(X28,k1_tops_1(X27,X29))
        | m2_connsp_2(X29,X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).

fof(c_0_17,plain,(
    ! [X26] :
      ( ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | k1_tops_1(X26,k2_struct_0(X26)) = k2_struct_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_tops_1])])).

fof(c_0_18,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | ~ v1_xboole_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_19,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ~ m2_connsp_2(k2_struct_0(esk3_0),esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_25,plain,
    ( m2_connsp_2(X3,X2,X1)
    | ~ r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k1_tops_1(X1,k2_struct_0(X1)) = k2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X24] :
      ( ~ l1_struct_0(X24)
      | k2_struct_0(X24) = u1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_28,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | l1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_29,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,X20)
      | v1_xboole_0(X20)
      | r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( ~ m2_connsp_2(k2_struct_0(esk3_0),esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( m2_connsp_2(k2_struct_0(X1),X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk4_0,k2_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_45,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk3_0)))
    | r2_hidden(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_31]),c_0_37])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:34:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.14/0.38  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.14/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.14/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.38  fof(t35_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>m2_connsp_2(k2_struct_0(X1),X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 0.14/0.38  fof(d2_connsp_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,X2)<=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 0.14/0.38  fof(t43_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>k1_tops_1(X1,k2_struct_0(X1))=k2_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 0.14/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.14/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.14/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.38  fof(c_0_11, plain, ![X18]:m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.14/0.38  fof(c_0_12, plain, ![X17]:k2_subset_1(X17)=X17, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.14/0.38  fof(c_0_13, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|r1_tarski(X12,X10)|X11!=k1_zfmisc_1(X10))&(~r1_tarski(X13,X10)|r2_hidden(X13,X11)|X11!=k1_zfmisc_1(X10)))&((~r2_hidden(esk2_2(X14,X15),X15)|~r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14))&(r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.38  fof(c_0_14, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.38  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>m2_connsp_2(k2_struct_0(X1),X1,X2)))), inference(assume_negation,[status(cth)],[t35_connsp_2])).
% 0.14/0.38  fof(c_0_16, plain, ![X27, X28, X29]:((~m2_connsp_2(X29,X27,X28)|r1_tarski(X28,k1_tops_1(X27,X29))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(~r1_tarski(X28,k1_tops_1(X27,X29))|m2_connsp_2(X29,X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).
% 0.14/0.38  fof(c_0_17, plain, ![X26]:(~v2_pre_topc(X26)|~l1_pre_topc(X26)|k1_tops_1(X26,k2_struct_0(X26))=k2_struct_0(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_tops_1])])).
% 0.14/0.38  fof(c_0_18, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|~v1_xboole_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.14/0.38  cnf(c_0_19, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_20, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_21, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  fof(c_0_24, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&~m2_connsp_2(k2_struct_0(esk3_0),esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.14/0.38  cnf(c_0_25, plain, (m2_connsp_2(X3,X2,X1)|~r1_tarski(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_26, plain, (k1_tops_1(X1,k2_struct_0(X1))=k2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  fof(c_0_27, plain, ![X24]:(~l1_struct_0(X24)|k2_struct_0(X24)=u1_struct_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.14/0.38  fof(c_0_28, plain, ![X25]:(~l1_pre_topc(X25)|l1_struct_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.38  fof(c_0_29, plain, ![X19, X20]:(~m1_subset_1(X19,X20)|(v1_xboole_0(X20)|r2_hidden(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.38  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.38  cnf(c_0_32, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (~m2_connsp_2(k2_struct_0(esk3_0),esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_35, plain, (m2_connsp_2(k2_struct_0(X1),X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_39, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_40, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_41, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  cnf(c_0_42, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.14/0.38  cnf(c_0_43, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (~m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk4_0,k2_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38])])).
% 0.14/0.38  cnf(c_0_45, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.38  cnf(c_0_46, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk3_0)))|r2_hidden(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_41, c_0_38])).
% 0.14/0.38  cnf(c_0_48, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (~r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_31]), c_0_37])])).
% 0.14/0.38  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_46])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[c_0_47, c_0_48])).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 53
% 0.14/0.38  # Proof object clause steps            : 30
% 0.14/0.38  # Proof object formula steps           : 23
% 0.14/0.38  # Proof object conjectures             : 12
% 0.14/0.38  # Proof object clause conjectures      : 9
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 16
% 0.14/0.38  # Proof object initial formulas used   : 11
% 0.14/0.38  # Proof object generating inferences   : 12
% 0.14/0.38  # Proof object simplifying inferences  : 11
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 11
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 21
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 20
% 0.14/0.38  # Processed clauses                    : 67
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 4
% 0.14/0.38  # ...remaining for further processing  : 63
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 1
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 62
% 0.14/0.38  # ...of the previous two non-trivial   : 54
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 59
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 40
% 0.14/0.38  #    Positive orientable unit clauses  : 7
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 5
% 0.14/0.38  #    Non-unit-clauses                  : 28
% 0.14/0.38  # Current number of unprocessed clauses: 24
% 0.14/0.38  # ...number of literals in the above   : 110
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 24
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 224
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 61
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.14/0.38  # Unit Clause-clause subsumption calls : 17
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 11
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2462
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.030 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.035 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
