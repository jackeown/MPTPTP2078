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
% DateTime   : Thu Dec  3 11:14:29 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 844 expanded)
%              Number of clauses        :   53 ( 325 expanded)
%              Number of leaves         :    9 ( 207 expanded)
%              Depth                    :   20
%              Number of atoms          :  386 (5831 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   66 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t8_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & r1_tarski(X4,X3)
                    & r2_hidden(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t57_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & r1_tarski(X4,X2)
                    & r2_hidden(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_1)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(c_0_9,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_10,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( m1_connsp_2(X3,X1,X2)
                <=> ? [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                      & v3_pre_topc(X4,X1)
                      & r1_tarski(X4,X3)
                      & r2_hidden(X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_connsp_2])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ! [X35] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
      & ( ~ m1_connsp_2(esk6_0,esk4_0,esk5_0)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ v3_pre_topc(X35,esk4_0)
        | ~ r1_tarski(X35,esk6_0)
        | ~ r2_hidden(esk5_0,X35) )
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | m1_connsp_2(esk6_0,esk4_0,esk5_0) )
      & ( v3_pre_topc(esk7_0,esk4_0)
        | m1_connsp_2(esk6_0,esk4_0,esk5_0) )
      & ( r1_tarski(esk7_0,esk6_0)
        | m1_connsp_2(esk6_0,esk4_0,esk5_0) )
      & ( r2_hidden(esk5_0,esk7_0)
        | m1_connsp_2(esk6_0,esk4_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( ~ m1_connsp_2(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r1_tarski(X1,esk6_0)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0)
    | m1_connsp_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X26,X27,X28] :
      ( ( ~ m1_connsp_2(X28,X26,X27)
        | r2_hidden(X27,k1_tops_1(X26,X28))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r2_hidden(X27,k1_tops_1(X26,X28))
        | m1_connsp_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_23,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | ~ m1_connsp_2(X31,X29,X30)
      | m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_13])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | v3_pre_topc(k1_tops_1(X10,X11),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_30,plain,(
    ! [X12,X13] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | r1_tarski(k1_tops_1(X12,X13),X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_31,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0)
    | m1_connsp_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_32,plain,(
    ! [X17,X18,X19,X21,X22,X24] :
      ( ( m1_subset_1(esk1_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r2_hidden(X19,X18)
        | ~ v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v3_pre_topc(esk1_3(X17,X18,X19),X17)
        | ~ r2_hidden(X19,X18)
        | ~ v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r1_tarski(esk1_3(X17,X18,X19),X18)
        | ~ r2_hidden(X19,X18)
        | ~ v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(X19,esk1_3(X17,X18,X19))
        | ~ r2_hidden(X19,X18)
        | ~ v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_pre_topc(X22,X17)
        | ~ r1_tarski(X22,X18)
        | ~ r2_hidden(X21,X22)
        | r2_hidden(X21,X18)
        | ~ v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_pre_topc(X24,X17)
        | ~ r1_tarski(X24,X18)
        | ~ r2_hidden(esk2_2(X17,X18),X24)
        | v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk3_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))
        | r2_hidden(esk2_2(X17,X18),X18)
        | v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v3_pre_topc(esk3_2(X17,X18),X17)
        | r2_hidden(esk2_2(X17,X18),X18)
        | v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r1_tarski(esk3_2(X17,X18),X18)
        | r2_hidden(esk2_2(X17,X18),X18)
        | v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk2_2(X17,X18),esk3_2(X17,X18))
        | r2_hidden(esk2_2(X17,X18),X18)
        | v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_tops_1])])])])])])).

cnf(c_0_33,negated_conjecture,
    ( v2_struct_0(X1)
    | r1_tarski(esk7_0,esk6_0)
    | ~ m1_connsp_2(X2,X1,esk5_0)
    | ~ v3_pre_topc(k1_tops_1(X1,X2),esk4_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk5_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_31]),c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | m1_connsp_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,plain,
    ( r2_hidden(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X4,X1)
    | ~ v3_pre_topc(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0)
    | ~ m1_connsp_2(X1,esk4_0,esk5_0)
    | ~ m1_subset_1(k1_tops_1(esk4_0,X1),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_41]),c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v3_pre_topc(X2,esk4_0)
    | ~ v3_pre_topc(X3,esk4_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r1_tarski(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35]),c_0_36])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_16]),c_0_35])]),c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( v2_struct_0(X1)
    | v3_pre_topc(esk7_0,esk4_0)
    | ~ m1_connsp_2(X2,X1,esk5_0)
    | ~ v3_pre_topc(k1_tops_1(X1,X2),esk4_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk5_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_28])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v3_pre_topc(X2,esk4_0)
    | ~ v3_pre_topc(X3,esk4_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_13])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0)
    | ~ m1_connsp_2(X1,esk4_0,esk5_0)
    | ~ m1_subset_1(k1_tops_1(esk4_0,X1),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_34]),c_0_35]),c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk5_0,esk7_0)
    | ~ m1_connsp_2(X2,X1,esk5_0)
    | ~ v3_pre_topc(k1_tops_1(X1,X2),esk4_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk5_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk7_0)
    | ~ v3_pre_topc(esk7_0,esk4_0)
    | ~ v3_pre_topc(X2,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_45]),c_0_16]),c_0_35])]),c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | ~ m1_connsp_2(X1,esk4_0,esk5_0)
    | ~ m1_subset_1(k1_tops_1(esk4_0,X1),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_34]),c_0_35]),c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk7_0)
    | ~ v3_pre_topc(X2,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_45]),c_0_16]),c_0_35])]),c_0_41])).

cnf(c_0_61,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( m1_connsp_2(X1,X2,esk5_0)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(k1_tops_1(X2,X1),esk4_0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(k1_tops_1(X2,X1),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_tops_1(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(esk5_0,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_64,plain,(
    ! [X14,X15,X16] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ v3_pre_topc(X15,X14)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(X15,k1_tops_1(X14,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_65,negated_conjecture,
    ( m1_connsp_2(X1,esk4_0,esk5_0)
    | ~ m1_subset_1(k1_tops_1(esk4_0,X1),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_tops_1(esk4_0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_34]),c_0_35]),c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_66,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( m1_connsp_2(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_tops_1(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_45]),c_0_16]),c_0_35])])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_tops_1(X2,X3)))
    | ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( m1_connsp_2(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_57]),c_0_35]),c_0_16]),c_0_53]),c_0_49])])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_69])]),c_0_21])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_49]),c_0_60]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.60/0.84  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.60/0.84  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.60/0.84  #
% 0.60/0.84  # Preprocessing time       : 0.040 s
% 0.60/0.84  
% 0.60/0.84  # Proof found!
% 0.60/0.84  # SZS status Theorem
% 0.60/0.84  # SZS output start CNFRefutation
% 0.60/0.84  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.60/0.84  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.60/0.84  fof(t8_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 0.60/0.84  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.60/0.84  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.60/0.84  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.60/0.84  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.60/0.84  fof(t57_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X2))&r2_hidden(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tops_1)).
% 0.60/0.84  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 0.60/0.84  fof(c_0_9, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.60/0.84  fof(c_0_10, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.60/0.84  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))))), inference(assume_negation,[status(cth)],[t8_connsp_2])).
% 0.60/0.84  cnf(c_0_12, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.60/0.84  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.60/0.84  fof(c_0_14, negated_conjecture, ![X35]:(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((~m1_connsp_2(esk6_0,esk4_0,esk5_0)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_pre_topc(X35,esk4_0)|~r1_tarski(X35,esk6_0)|~r2_hidden(esk5_0,X35)))&((((m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))|m1_connsp_2(esk6_0,esk4_0,esk5_0))&(v3_pre_topc(esk7_0,esk4_0)|m1_connsp_2(esk6_0,esk4_0,esk5_0)))&(r1_tarski(esk7_0,esk6_0)|m1_connsp_2(esk6_0,esk4_0,esk5_0)))&(r2_hidden(esk5_0,esk7_0)|m1_connsp_2(esk6_0,esk4_0,esk5_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).
% 0.60/0.84  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.60/0.84  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.84  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.60/0.84  cnf(c_0_18, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk4_0))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.60/0.84  cnf(c_0_19, negated_conjecture, (~m1_connsp_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_pre_topc(X1,esk4_0)|~r1_tarski(X1,esk6_0)|~r2_hidden(esk5_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.84  cnf(c_0_20, negated_conjecture, (r1_tarski(esk7_0,esk6_0)|m1_connsp_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.84  cnf(c_0_21, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.60/0.84  fof(c_0_22, plain, ![X26, X27, X28]:((~m1_connsp_2(X28,X26,X27)|r2_hidden(X27,k1_tops_1(X26,X28))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r2_hidden(X27,k1_tops_1(X26,X28))|m1_connsp_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.60/0.84  fof(c_0_23, plain, ![X29, X30, X31]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_subset_1(X30,u1_struct_0(X29))|(~m1_connsp_2(X31,X29,X30)|m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.60/0.84  cnf(c_0_24, negated_conjecture, (r1_tarski(esk7_0,esk6_0)|~r2_hidden(esk5_0,X1)|~v3_pre_topc(X1,esk4_0)|~r1_tarski(X1,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.60/0.84  cnf(c_0_25, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.60/0.84  cnf(c_0_26, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.60/0.84  cnf(c_0_27, negated_conjecture, (r1_tarski(esk7_0,esk6_0)|~r2_hidden(esk5_0,X1)|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_24, c_0_13])).
% 0.60/0.84  cnf(c_0_28, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_25, c_0_26])).
% 0.60/0.84  fof(c_0_29, plain, ![X10, X11]:(~v2_pre_topc(X10)|~l1_pre_topc(X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|v3_pre_topc(k1_tops_1(X10,X11),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.60/0.84  fof(c_0_30, plain, ![X12, X13]:(~l1_pre_topc(X12)|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|r1_tarski(k1_tops_1(X12,X13),X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.60/0.84  cnf(c_0_31, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)|m1_connsp_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.84  fof(c_0_32, plain, ![X17, X18, X19, X21, X22, X24]:((((((m1_subset_1(esk1_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))|~r2_hidden(X19,X18)|~v3_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(v3_pre_topc(esk1_3(X17,X18,X19),X17)|~r2_hidden(X19,X18)|~v3_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(r1_tarski(esk1_3(X17,X18,X19),X18)|~r2_hidden(X19,X18)|~v3_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(r2_hidden(X19,esk1_3(X17,X18,X19))|~r2_hidden(X19,X18)|~v3_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X17)))|~v3_pre_topc(X22,X17)|~r1_tarski(X22,X18)|~r2_hidden(X21,X22)|r2_hidden(X21,X18)|~v3_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))))&((~r2_hidden(esk2_2(X17,X18),X18)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X17)))|~v3_pre_topc(X24,X17)|~r1_tarski(X24,X18)|~r2_hidden(esk2_2(X17,X18),X24))|v3_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((((m1_subset_1(esk3_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))|r2_hidden(esk2_2(X17,X18),X18)|v3_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(v3_pre_topc(esk3_2(X17,X18),X17)|r2_hidden(esk2_2(X17,X18),X18)|v3_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(r1_tarski(esk3_2(X17,X18),X18)|r2_hidden(esk2_2(X17,X18),X18)|v3_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(r2_hidden(esk2_2(X17,X18),esk3_2(X17,X18))|r2_hidden(esk2_2(X17,X18),X18)|v3_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_tops_1])])])])])])).
% 0.60/0.84  cnf(c_0_33, negated_conjecture, (v2_struct_0(X1)|r1_tarski(esk7_0,esk6_0)|~m1_connsp_2(X2,X1,esk5_0)|~v3_pre_topc(k1_tops_1(X1,X2),esk4_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(esk6_0))|~m1_subset_1(esk5_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.60/0.84  cnf(c_0_34, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.60/0.84  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.84  cnf(c_0_36, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.84  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.84  cnf(c_0_38, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.84  cnf(c_0_39, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.60/0.84  cnf(c_0_40, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)|~r2_hidden(esk5_0,X1)|~v3_pre_topc(X1,esk4_0)|~r1_tarski(X1,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_31]), c_0_21])).
% 0.60/0.84  cnf(c_0_41, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|m1_connsp_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.84  cnf(c_0_42, plain, (r2_hidden(X4,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r1_tarski(X1,X3)|~r2_hidden(X4,X1)|~v3_pre_topc(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.60/0.84  cnf(c_0_43, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_21, c_0_13])).
% 0.60/0.84  cnf(c_0_44, negated_conjecture, (r1_tarski(esk7_0,esk6_0)|~m1_connsp_2(X1,esk4_0,esk5_0)|~m1_subset_1(k1_tops_1(esk4_0,X1),k1_zfmisc_1(esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37])]), c_0_38])).
% 0.60/0.84  cnf(c_0_45, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_17, c_0_39])).
% 0.60/0.84  cnf(c_0_46, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)|~r2_hidden(esk5_0,X1)|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_40, c_0_13])).
% 0.60/0.84  cnf(c_0_47, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk5_0,X1)|~v3_pre_topc(X1,esk4_0)|~r1_tarski(X1,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_41]), c_0_21])).
% 0.60/0.84  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~v3_pre_topc(X2,esk4_0)|~v3_pre_topc(X3,esk4_0)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X2,k1_zfmisc_1(esk6_0))|~r1_tarski(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_35]), c_0_36])])).
% 0.60/0.84  cnf(c_0_49, negated_conjecture, (r1_tarski(esk7_0,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_16]), c_0_35])]), c_0_20])).
% 0.60/0.84  cnf(c_0_50, negated_conjecture, (v2_struct_0(X1)|v3_pre_topc(esk7_0,esk4_0)|~m1_connsp_2(X2,X1,esk5_0)|~v3_pre_topc(k1_tops_1(X1,X2),esk4_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(esk6_0))|~m1_subset_1(esk5_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_46, c_0_28])).
% 0.60/0.84  cnf(c_0_51, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk5_0,X1)|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_47, c_0_13])).
% 0.60/0.84  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~v3_pre_topc(X2,esk4_0)|~v3_pre_topc(X3,esk4_0)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X2,k1_zfmisc_1(esk6_0))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_48, c_0_13])).
% 0.60/0.84  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_21, c_0_49])).
% 0.60/0.84  cnf(c_0_54, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)|~m1_connsp_2(X1,esk4_0,esk5_0)|~m1_subset_1(k1_tops_1(esk4_0,X1),k1_zfmisc_1(esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_34]), c_0_35]), c_0_36]), c_0_37])]), c_0_38])).
% 0.60/0.84  cnf(c_0_55, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk5_0,esk7_0)|~m1_connsp_2(X2,X1,esk5_0)|~v3_pre_topc(k1_tops_1(X1,X2),esk4_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(esk6_0))|~m1_subset_1(esk5_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_51, c_0_28])).
% 0.60/0.84  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,esk7_0)|~v3_pre_topc(esk7_0,esk4_0)|~v3_pre_topc(X2,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(esk6_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.60/0.84  cnf(c_0_57, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_45]), c_0_16]), c_0_35])]), c_0_31])).
% 0.60/0.84  cnf(c_0_58, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|~m1_connsp_2(X1,esk4_0,esk5_0)|~m1_subset_1(k1_tops_1(esk4_0,X1),k1_zfmisc_1(esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_34]), c_0_35]), c_0_36]), c_0_37])]), c_0_38])).
% 0.60/0.84  cnf(c_0_59, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,esk7_0)|~v3_pre_topc(X2,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(esk6_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.60/0.84  cnf(c_0_60, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_45]), c_0_16]), c_0_35])]), c_0_41])).
% 0.60/0.84  cnf(c_0_61, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.60/0.84  cnf(c_0_62, negated_conjecture, (r2_hidden(esk5_0,X1)|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk6_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.60/0.84  cnf(c_0_63, negated_conjecture, (m1_connsp_2(X1,X2,esk5_0)|v2_struct_0(X2)|~v3_pre_topc(k1_tops_1(X2,X1),esk4_0)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(k1_tops_1(X2,X1),k1_zfmisc_1(esk6_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(k1_tops_1(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(esk5_0,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.60/0.84  fof(c_0_64, plain, ![X14, X15, X16]:(~l1_pre_topc(X14)|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(~v3_pre_topc(X15,X14)|~r1_tarski(X15,X16)|r1_tarski(X15,k1_tops_1(X14,X16)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 0.60/0.84  cnf(c_0_65, negated_conjecture, (m1_connsp_2(X1,esk4_0,esk5_0)|~m1_subset_1(k1_tops_1(esk4_0,X1),k1_zfmisc_1(esk6_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(k1_tops_1(esk4_0,X1)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_34]), c_0_35]), c_0_36]), c_0_37])]), c_0_38])).
% 0.60/0.84  cnf(c_0_66, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.60/0.84  cnf(c_0_67, negated_conjecture, (m1_connsp_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k1_tops_1(esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_45]), c_0_16]), c_0_35])])).
% 0.60/0.84  cnf(c_0_68, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_tops_1(X2,X3)))|~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_17, c_0_66])).
% 0.60/0.84  cnf(c_0_69, negated_conjecture, (m1_connsp_2(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_57]), c_0_35]), c_0_16]), c_0_53]), c_0_49])])).
% 0.60/0.84  cnf(c_0_70, negated_conjecture, (~r2_hidden(esk5_0,X1)|~v3_pre_topc(X1,esk4_0)|~r1_tarski(X1,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_69])]), c_0_21])).
% 0.60/0.84  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_49]), c_0_60]), c_0_57])]), ['proof']).
% 0.60/0.84  # SZS output end CNFRefutation
% 0.60/0.84  # Proof object total steps             : 72
% 0.60/0.84  # Proof object clause steps            : 53
% 0.60/0.84  # Proof object formula steps           : 19
% 0.60/0.84  # Proof object conjectures             : 42
% 0.60/0.84  # Proof object clause conjectures      : 39
% 0.60/0.84  # Proof object formula conjectures     : 3
% 0.60/0.84  # Proof object initial clauses used    : 19
% 0.60/0.84  # Proof object initial formulas used   : 9
% 0.60/0.84  # Proof object generating inferences   : 31
% 0.60/0.84  # Proof object simplifying inferences  : 56
% 0.60/0.84  # Training examples: 0 positive, 0 negative
% 0.60/0.84  # Parsed axioms                        : 9
% 0.60/0.84  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.84  # Initial clauses                      : 29
% 0.60/0.84  # Removed in clause preprocessing      : 0
% 0.60/0.84  # Initial clauses in saturation        : 29
% 0.60/0.84  # Processed clauses                    : 2994
% 0.60/0.84  # ...of these trivial                  : 6
% 0.60/0.84  # ...subsumed                          : 2144
% 0.60/0.84  # ...remaining for further processing  : 844
% 0.60/0.84  # Other redundant clauses eliminated   : 0
% 0.60/0.84  # Clauses deleted for lack of memory   : 0
% 0.60/0.84  # Backward-subsumed                    : 81
% 0.60/0.84  # Backward-rewritten                   : 47
% 0.60/0.84  # Generated clauses                    : 17818
% 0.60/0.84  # ...of the previous two non-trivial   : 16950
% 0.60/0.84  # Contextual simplify-reflections      : 65
% 0.60/0.84  # Paramodulations                      : 17818
% 0.60/0.84  # Factorizations                       : 0
% 0.60/0.84  # Equation resolutions                 : 0
% 0.60/0.84  # Propositional unsat checks           : 0
% 0.60/0.84  #    Propositional check models        : 0
% 0.60/0.84  #    Propositional check unsatisfiable : 0
% 0.60/0.84  #    Propositional clauses             : 0
% 0.60/0.84  #    Propositional clauses after purity: 0
% 0.60/0.84  #    Propositional unsat core size     : 0
% 0.60/0.84  #    Propositional preprocessing time  : 0.000
% 0.60/0.84  #    Propositional encoding time       : 0.000
% 0.60/0.84  #    Propositional solver time         : 0.000
% 0.60/0.84  #    Success case prop preproc time    : 0.000
% 0.60/0.84  #    Success case prop encoding time   : 0.000
% 0.60/0.84  #    Success case prop solver time     : 0.000
% 0.60/0.84  # Current number of processed clauses  : 716
% 0.60/0.84  #    Positive orientable unit clauses  : 10
% 0.60/0.84  #    Positive unorientable unit clauses: 0
% 0.60/0.84  #    Negative unit clauses             : 3
% 0.60/0.84  #    Non-unit-clauses                  : 703
% 0.60/0.84  # Current number of unprocessed clauses: 13656
% 0.60/0.84  # ...number of literals in the above   : 147510
% 0.60/0.84  # Current number of archived formulas  : 0
% 0.60/0.84  # Current number of archived clauses   : 128
% 0.60/0.84  # Clause-clause subsumption calls (NU) : 145179
% 0.60/0.84  # Rec. Clause-clause subsumption calls : 21167
% 0.60/0.84  # Non-unit clause-clause subsumptions  : 1938
% 0.60/0.84  # Unit Clause-clause subsumption calls : 260
% 0.60/0.84  # Rewrite failures with RHS unbound    : 0
% 0.60/0.84  # BW rewrite match attempts            : 7
% 0.60/0.84  # BW rewrite match successes           : 6
% 0.60/0.84  # Condensation attempts                : 0
% 0.60/0.84  # Condensation successes               : 0
% 0.60/0.84  # Termbank termtop insertions          : 640135
% 0.60/0.84  
% 0.60/0.84  # -------------------------------------------------
% 0.60/0.84  # User time                : 0.486 s
% 0.60/0.84  # System time              : 0.019 s
% 0.60/0.84  # Total time               : 0.505 s
% 0.60/0.84  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
