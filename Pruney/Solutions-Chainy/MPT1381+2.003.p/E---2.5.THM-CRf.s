%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:22 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  56 expanded)
%              Number of clauses        :   21 (  22 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :  135 ( 283 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( m1_connsp_2(X2,X1,X3)
               => r2_hidden(X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( m1_connsp_2(X2,X1,X3)
                 => r2_hidden(X3,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_connsp_2])).

fof(c_0_7,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | r1_tarski(k1_tops_1(X16,X17),X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_connsp_2(esk3_0,esk2_0,esk4_0)
    & ~ r2_hidden(esk4_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_9,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X18,X19,X20] :
      ( ( ~ m1_connsp_2(X20,X18,X19)
        | r2_hidden(X19,k1_tops_1(X18,X20))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ r2_hidden(X19,k1_tops_1(X18,X20))
        | m1_connsp_2(X20,X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_12,plain,(
    ! [X21,X22,X23] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | ~ m1_connsp_2(X23,X21,X22)
      | m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k3_xboole_0(X14,X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k3_xboole_0(k1_tops_1(esk2_0,esk3_0),esk3_0) = k1_tops_1(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,X2))
    | ~ m1_connsp_2(X2,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_10])]),c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( m1_connsp_2(esk3_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk4_0,k1_tops_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.21/0.37  # and selection function HSelectMinInfpos.
% 0.21/0.37  #
% 0.21/0.37  # Preprocessing time       : 0.027 s
% 0.21/0.37  # Presaturation interreduction done
% 0.21/0.37  
% 0.21/0.37  # Proof found!
% 0.21/0.37  # SZS status Theorem
% 0.21/0.37  # SZS output start CNFRefutation
% 0.21/0.37  fof(t6_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(m1_connsp_2(X2,X1,X3)=>r2_hidden(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 0.21/0.37  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.21/0.37  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.21/0.37  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.21/0.37  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.21/0.37  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(m1_connsp_2(X2,X1,X3)=>r2_hidden(X3,X2)))))), inference(assume_negation,[status(cth)],[t6_connsp_2])).
% 0.21/0.37  fof(c_0_7, plain, ![X16, X17]:(~l1_pre_topc(X16)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|r1_tarski(k1_tops_1(X16,X17),X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.21/0.37  fof(c_0_8, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_connsp_2(esk3_0,esk2_0,esk4_0)&~r2_hidden(esk4_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.21/0.37  cnf(c_0_9, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.37  cnf(c_0_10, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.37  fof(c_0_11, plain, ![X18, X19, X20]:((~m1_connsp_2(X20,X18,X19)|r2_hidden(X19,k1_tops_1(X18,X20))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(~r2_hidden(X19,k1_tops_1(X18,X20))|m1_connsp_2(X20,X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.21/0.37  fof(c_0_12, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|~m1_subset_1(X22,u1_struct_0(X21))|(~m1_connsp_2(X23,X21,X22)|m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.21/0.37  fof(c_0_13, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.21/0.37  fof(c_0_14, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k3_xboole_0(X14,X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.37  cnf(c_0_15, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.21/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.37  cnf(c_0_17, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.37  cnf(c_0_18, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.37  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.37  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.37  cnf(c_0_21, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.37  cnf(c_0_22, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.37  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.37  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.37  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.21/0.37  cnf(c_0_26, negated_conjecture, (k3_xboole_0(k1_tops_1(esk2_0,esk3_0),esk3_0)=k1_tops_1(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.37  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,X2))|~m1_connsp_2(X2,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_10])]), c_0_24])).
% 0.21/0.37  cnf(c_0_28, negated_conjecture, (m1_connsp_2(esk3_0,esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.37  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.37  cnf(c_0_31, negated_conjecture, (r2_hidden(esk4_0,k1_tops_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.21/0.37  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.37  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), ['proof']).
% 0.21/0.37  # SZS output end CNFRefutation
% 0.21/0.37  # Proof object total steps             : 34
% 0.21/0.37  # Proof object clause steps            : 21
% 0.21/0.37  # Proof object formula steps           : 13
% 0.21/0.37  # Proof object conjectures             : 17
% 0.21/0.37  # Proof object clause conjectures      : 14
% 0.21/0.37  # Proof object formula conjectures     : 3
% 0.21/0.37  # Proof object initial clauses used    : 12
% 0.21/0.37  # Proof object initial formulas used   : 6
% 0.21/0.37  # Proof object generating inferences   : 7
% 0.21/0.37  # Proof object simplifying inferences  : 8
% 0.21/0.37  # Training examples: 0 positive, 0 negative
% 0.21/0.37  # Parsed axioms                        : 6
% 0.21/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.37  # Initial clauses                      : 18
% 0.21/0.37  # Removed in clause preprocessing      : 0
% 0.21/0.37  # Initial clauses in saturation        : 18
% 0.21/0.37  # Processed clauses                    : 53
% 0.21/0.37  # ...of these trivial                  : 0
% 0.21/0.37  # ...subsumed                          : 2
% 0.21/0.37  # ...remaining for further processing  : 51
% 0.21/0.37  # Other redundant clauses eliminated   : 3
% 0.21/0.37  # Clauses deleted for lack of memory   : 0
% 0.21/0.37  # Backward-subsumed                    : 0
% 0.21/0.37  # Backward-rewritten                   : 0
% 0.21/0.37  # Generated clauses                    : 51
% 0.21/0.37  # ...of the previous two non-trivial   : 44
% 0.21/0.37  # Contextual simplify-reflections      : 1
% 0.21/0.37  # Paramodulations                      : 44
% 0.21/0.37  # Factorizations                       : 4
% 0.21/0.37  # Equation resolutions                 : 3
% 0.21/0.37  # Propositional unsat checks           : 0
% 0.21/0.37  #    Propositional check models        : 0
% 0.21/0.37  #    Propositional check unsatisfiable : 0
% 0.21/0.37  #    Propositional clauses             : 0
% 0.21/0.37  #    Propositional clauses after purity: 0
% 0.21/0.37  #    Propositional unsat core size     : 0
% 0.21/0.37  #    Propositional preprocessing time  : 0.000
% 0.21/0.37  #    Propositional encoding time       : 0.000
% 0.21/0.37  #    Propositional solver time         : 0.000
% 0.21/0.37  #    Success case prop preproc time    : 0.000
% 0.21/0.37  #    Success case prop encoding time   : 0.000
% 0.21/0.37  #    Success case prop solver time     : 0.000
% 0.21/0.37  # Current number of processed clauses  : 30
% 0.21/0.37  #    Positive orientable unit clauses  : 8
% 0.21/0.37  #    Positive unorientable unit clauses: 0
% 0.21/0.37  #    Negative unit clauses             : 2
% 0.21/0.37  #    Non-unit-clauses                  : 20
% 0.21/0.37  # Current number of unprocessed clauses: 26
% 0.21/0.37  # ...number of literals in the above   : 77
% 0.21/0.37  # Current number of archived formulas  : 0
% 0.21/0.37  # Current number of archived clauses   : 18
% 0.21/0.37  # Clause-clause subsumption calls (NU) : 111
% 0.21/0.37  # Rec. Clause-clause subsumption calls : 67
% 0.21/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.21/0.37  # Unit Clause-clause subsumption calls : 4
% 0.21/0.37  # Rewrite failures with RHS unbound    : 0
% 0.21/0.37  # BW rewrite match attempts            : 0
% 0.21/0.37  # BW rewrite match successes           : 0
% 0.21/0.37  # Condensation attempts                : 0
% 0.21/0.37  # Condensation successes               : 0
% 0.21/0.37  # Termbank termtop insertions          : 2310
% 0.21/0.37  
% 0.21/0.37  # -------------------------------------------------
% 0.21/0.37  # User time                : 0.028 s
% 0.21/0.37  # System time              : 0.005 s
% 0.21/0.37  # Total time               : 0.033 s
% 0.21/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
