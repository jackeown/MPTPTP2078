%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:24 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 214 expanded)
%              Number of clauses        :   32 (  79 expanded)
%              Number of leaves         :    8 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  175 (1370 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ~ ( m1_connsp_2(X3,X1,X2)
                  & ! [X4] :
                      ( ( ~ v1_xboole_0(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                     => ~ ( m1_connsp_2(X4,X1,X2)
                          & v3_pre_topc(X4,X1)
                          & r1_tarski(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( m1_connsp_2(X3,X1,X2)
                    & ! [X4] :
                        ( ( ~ v1_xboole_0(X4)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                       => ~ ( m1_connsp_2(X4,X1,X2)
                            & v3_pre_topc(X4,X1)
                            & r1_tarski(X4,X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_connsp_2])).

fof(c_0_9,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | r1_tarski(k1_tops_1(X19,X20),X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_10,negated_conjecture,(
    ! [X30] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & m1_connsp_2(esk5_0,esk3_0,esk4_0)
      & ( v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ m1_connsp_2(X30,esk3_0,esk4_0)
        | ~ v3_pre_topc(X30,esk3_0)
        | ~ r1_tarski(X30,esk5_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X21,X22,X23] :
      ( ( ~ m1_connsp_2(X23,X21,X22)
        | r2_hidden(X22,k1_tops_1(X21,X23))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r2_hidden(X22,k1_tops_1(X21,X23))
        | m1_connsp_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk5_0),X1)
    | r2_hidden(esk2_2(k1_tops_1(esk3_0,esk5_0),X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk5_0),X1)
    | r2_hidden(esk2_2(k1_tops_1(esk3_0,esk5_0),X1),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_30,plain,(
    ! [X17,X18] :
      ( ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | v3_pre_topc(k1_tops_1(X17,X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_31,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,esk5_0))
    | ~ m1_connsp_2(esk5_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_15]),c_0_26])]),c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( m1_connsp_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_0,k1_tops_1(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

fof(c_0_40,plain,(
    ! [X24,X25,X26] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ m1_subset_1(X26,u1_struct_0(X24))
      | ~ v3_pre_topc(X25,X24)
      | ~ r2_hidden(X26,X25)
      | m1_connsp_2(X25,X24,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_connsp_2(X1,esk3_0,esk4_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk3_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk3_0,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_14]),c_0_15]),c_0_26])])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(k1_tops_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( ~ m1_connsp_2(k1_tops_1(esk3_0,esk5_0),esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_18])]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( m1_connsp_2(k1_tops_1(esk3_0,esk5_0),esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_42]),c_0_43]),c_0_15]),c_0_26])]),c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_34]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:12:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S033N
% 0.12/0.35  # and selection function PSelectUnlessUniqMax.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.013 s
% 0.12/0.35  # Presaturation interreduction done
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(t7_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X3,X1,X2)&![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))=>~(((m1_connsp_2(X4,X1,X2)&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 0.12/0.35  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.12/0.35  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.35  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.35  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.12/0.35  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.12/0.35  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.35  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.12/0.35  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X3,X1,X2)&![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))=>~(((m1_connsp_2(X4,X1,X2)&v3_pre_topc(X4,X1))&r1_tarski(X4,X3)))))))))), inference(assume_negation,[status(cth)],[t7_connsp_2])).
% 0.12/0.35  fof(c_0_9, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|r1_tarski(k1_tops_1(X19,X20),X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.12/0.35  fof(c_0_10, negated_conjecture, ![X30]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_connsp_2(esk5_0,esk3_0,esk4_0)&(v1_xboole_0(X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(esk3_0)))|(~m1_connsp_2(X30,esk3_0,esk4_0)|~v3_pre_topc(X30,esk3_0)|~r1_tarski(X30,esk5_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.12/0.35  fof(c_0_11, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.35  fof(c_0_12, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.35  cnf(c_0_13, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.35  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.35  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_18, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.12/0.35  cnf(c_0_19, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_16, c_0_14])).
% 0.12/0.35  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k1_tops_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.35  cnf(c_0_21, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  fof(c_0_22, plain, ![X21, X22, X23]:((~m1_connsp_2(X23,X21,X22)|r2_hidden(X22,k1_tops_1(X21,X23))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~r2_hidden(X22,k1_tops_1(X21,X23))|m1_connsp_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.12/0.35  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_19])).
% 0.12/0.35  cnf(c_0_24, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk5_0),X1)|r2_hidden(esk2_2(k1_tops_1(esk3_0,esk5_0),X1),esk5_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.35  cnf(c_0_25, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.35  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_29, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk5_0),X1)|r2_hidden(esk2_2(k1_tops_1(esk3_0,esk5_0),X1),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.35  fof(c_0_30, plain, ![X17, X18]:(~v2_pre_topc(X17)|~l1_pre_topc(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|v3_pre_topc(k1_tops_1(X17,X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.12/0.35  fof(c_0_31, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.35  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,esk5_0))|~m1_connsp_2(esk5_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_14]), c_0_15]), c_0_26])]), c_0_27])).
% 0.12/0.35  cnf(c_0_33, negated_conjecture, (m1_connsp_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_35, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.35  cnf(c_0_36, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.35  cnf(c_0_37, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.35  cnf(c_0_38, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.35  cnf(c_0_39, negated_conjecture, (r2_hidden(esk4_0,k1_tops_1(esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.12/0.35  fof(c_0_40, plain, ![X24, X25, X26]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~m1_subset_1(X26,u1_struct_0(X24))|(~v3_pre_topc(X25,X24)|~r2_hidden(X26,X25)|m1_connsp_2(X25,X24,X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.12/0.35  cnf(c_0_41, negated_conjecture, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_connsp_2(X1,esk3_0,esk4_0)|~v3_pre_topc(X1,esk3_0)|~r1_tarski(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_42, negated_conjecture, (m1_subset_1(k1_tops_1(esk3_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.35  cnf(c_0_43, negated_conjecture, (v3_pre_topc(k1_tops_1(esk3_0,esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_14]), c_0_15]), c_0_26])])).
% 0.12/0.35  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(k1_tops_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.35  cnf(c_0_45, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.35  cnf(c_0_46, negated_conjecture, (~m1_connsp_2(k1_tops_1(esk3_0,esk5_0),esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_18])]), c_0_44])).
% 0.12/0.35  cnf(c_0_47, negated_conjecture, (m1_connsp_2(k1_tops_1(esk3_0,esk5_0),esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k1_tops_1(esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_42]), c_0_43]), c_0_15]), c_0_26])]), c_0_27])).
% 0.12/0.35  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_34]), c_0_39])]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 49
% 0.12/0.35  # Proof object clause steps            : 32
% 0.12/0.35  # Proof object formula steps           : 17
% 0.12/0.35  # Proof object conjectures             : 25
% 0.12/0.35  # Proof object clause conjectures      : 22
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 17
% 0.12/0.35  # Proof object initial formulas used   : 8
% 0.12/0.35  # Proof object generating inferences   : 15
% 0.12/0.35  # Proof object simplifying inferences  : 23
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 8
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 19
% 0.12/0.35  # Removed in clause preprocessing      : 0
% 0.12/0.35  # Initial clauses in saturation        : 19
% 0.12/0.35  # Processed clauses                    : 100
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 16
% 0.12/0.35  # ...remaining for further processing  : 84
% 0.12/0.35  # Other redundant clauses eliminated   : 0
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 1
% 0.12/0.35  # Generated clauses                    : 86
% 0.12/0.35  # ...of the previous two non-trivial   : 77
% 0.12/0.35  # Contextual simplify-reflections      : 0
% 0.12/0.35  # Paramodulations                      : 85
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 0
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 63
% 0.12/0.35  #    Positive orientable unit clauses  : 19
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 6
% 0.12/0.35  #    Non-unit-clauses                  : 38
% 0.12/0.35  # Current number of unprocessed clauses: 14
% 0.12/0.35  # ...number of literals in the above   : 53
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 21
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 346
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 143
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 3
% 0.12/0.35  # Unit Clause-clause subsumption calls : 87
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 12
% 0.12/0.35  # BW rewrite match successes           : 1
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 3341
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.013 s
% 0.12/0.35  # System time              : 0.005 s
% 0.12/0.35  # Total time               : 0.018 s
% 0.12/0.35  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
