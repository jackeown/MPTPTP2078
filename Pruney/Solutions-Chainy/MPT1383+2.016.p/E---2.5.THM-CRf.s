%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:28 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 (1248 expanded)
%              Number of clauses        :   50 ( 463 expanded)
%              Number of leaves         :   10 ( 298 expanded)
%              Depth                    :   17
%              Number of atoms          :  343 (9172 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   66 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,negated_conjecture,(
    ! [X39] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
      & ( ~ m1_connsp_2(esk6_0,esk4_0,esk5_0)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ v3_pre_topc(X39,esk4_0)
        | ~ r1_tarski(X39,esk6_0)
        | ~ r2_hidden(esk5_0,X39) )
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | m1_connsp_2(esk6_0,esk4_0,esk5_0) )
      & ( v3_pre_topc(esk7_0,esk4_0)
        | m1_connsp_2(esk6_0,esk4_0,esk5_0) )
      & ( r1_tarski(esk7_0,esk6_0)
        | m1_connsp_2(esk6_0,esk4_0,esk5_0) )
      & ( r2_hidden(esk5_0,esk7_0)
        | m1_connsp_2(esk6_0,esk4_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

fof(c_0_13,plain,(
    ! [X30,X31,X32] :
      ( ( ~ m1_connsp_2(X32,X30,X31)
        | r2_hidden(X31,k1_tops_1(X30,X32))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ r2_hidden(X31,k1_tops_1(X30,X32))
        | m1_connsp_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_14,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_connsp_2(X35,X33,X34)
      | m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_15,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | r1_tarski(k1_tops_1(X12,X13),X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | v3_pre_topc(k1_tops_1(X10,X11),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk4_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_17]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( ~ m1_connsp_2(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r1_tarski(X1,esk6_0)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0)
    | m1_connsp_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_0,k1_tops_1(esk4_0,X1))
    | ~ m1_connsp_2(X1,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_24]),c_0_27])]),c_0_28])).

cnf(c_0_35,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk4_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk5_0,k1_tops_1(esk4_0,esk6_0))
    | r1_tarski(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk4_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_17]),c_0_24]),c_0_27])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk4_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_42,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ v3_pre_topc(X20,X18)
        | k1_tops_1(X18,X20) = X20
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X18)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( k1_tops_1(X17,X19) != X19
        | v3_pre_topc(X19,X17)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X18)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_31])])).

cnf(c_0_44,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0)
    | m1_connsp_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_45,plain,(
    ! [X14,X15,X16] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ r1_tarski(X15,X16)
      | r1_tarski(k1_tops_1(X14,X15),k1_tops_1(X14,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_46,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk5_0,k1_tops_1(esk4_0,esk6_0))
    | v3_pre_topc(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_44])).

fof(c_0_50,plain,(
    ! [X21,X22,X23,X25,X26,X28] :
      ( ( m1_subset_1(esk1_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(X23,X22)
        | ~ v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( v3_pre_topc(esk1_3(X21,X22,X23),X21)
        | ~ r2_hidden(X23,X22)
        | ~ v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r1_tarski(esk1_3(X21,X22,X23),X22)
        | ~ r2_hidden(X23,X22)
        | ~ v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(X23,esk1_3(X21,X22,X23))
        | ~ r2_hidden(X23,X22)
        | ~ v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v3_pre_topc(X26,X21)
        | ~ r1_tarski(X26,X22)
        | ~ r2_hidden(X25,X26)
        | r2_hidden(X25,X22)
        | ~ v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r2_hidden(esk2_2(X21,X22),X22)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v3_pre_topc(X28,X21)
        | ~ r1_tarski(X28,X22)
        | ~ r2_hidden(esk2_2(X21,X22),X28)
        | v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk3_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))
        | r2_hidden(esk2_2(X21,X22),X22)
        | v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( v3_pre_topc(esk3_2(X21,X22),X21)
        | r2_hidden(esk2_2(X21,X22),X22)
        | v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r1_tarski(esk3_2(X21,X22),X22)
        | r2_hidden(esk2_2(X21,X22),X22)
        | v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk2_2(X21,X22),esk3_2(X21,X22))
        | r2_hidden(esk2_2(X21,X22),X22)
        | v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_tops_1])])])])])])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_17]),c_0_24]),c_0_27])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_40]),c_0_41]),c_0_31])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | m1_connsp_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_56,plain,
    ( r2_hidden(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X4,X1)
    | ~ v3_pre_topc(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk4_0,X1),k1_tops_1(esk4_0,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_17]),c_0_24])])).

cnf(c_0_58,negated_conjecture,
    ( k1_tops_1(esk4_0,esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_24])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk4_0,esk6_0))
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X2,k1_tops_1(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_41]),c_0_40]),c_0_24]),c_0_27])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk7_0,k1_tops_1(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_43]),c_0_58]),c_0_53])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk5_0,k1_tops_1(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_40]),c_0_41]),c_0_31])])).

cnf(c_0_63,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk4_0,esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_54]),c_0_53]),c_0_61])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_55]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( m1_connsp_2(X1,esk4_0,esk5_0)
    | ~ r2_hidden(esk5_0,k1_tops_1(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_26]),c_0_24]),c_0_27])]),c_0_28])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk5_0,k1_tops_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( m1_connsp_2(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_17])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_68])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_65]),c_0_54]),c_0_53]),c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:25:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.38  # and selection function SelectNewComplexAHPNS.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t8_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.19/0.38  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.19/0.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.38  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.19/0.38  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.19/0.38  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 0.19/0.38  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.19/0.38  fof(t57_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X2))&r2_hidden(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tops_1)).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))))), inference(assume_negation,[status(cth)],[t8_connsp_2])).
% 0.19/0.38  fof(c_0_11, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  fof(c_0_12, negated_conjecture, ![X39]:(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((~m1_connsp_2(esk6_0,esk4_0,esk5_0)|(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_pre_topc(X39,esk4_0)|~r1_tarski(X39,esk6_0)|~r2_hidden(esk5_0,X39)))&((((m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))|m1_connsp_2(esk6_0,esk4_0,esk5_0))&(v3_pre_topc(esk7_0,esk4_0)|m1_connsp_2(esk6_0,esk4_0,esk5_0)))&(r1_tarski(esk7_0,esk6_0)|m1_connsp_2(esk6_0,esk4_0,esk5_0)))&(r2_hidden(esk5_0,esk7_0)|m1_connsp_2(esk6_0,esk4_0,esk5_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).
% 0.19/0.38  fof(c_0_13, plain, ![X30, X31, X32]:((~m1_connsp_2(X32,X30,X31)|r2_hidden(X31,k1_tops_1(X30,X32))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))&(~r2_hidden(X31,k1_tops_1(X30,X32))|m1_connsp_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.19/0.38  fof(c_0_14, plain, ![X33, X34, X35]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,u1_struct_0(X33))|(~m1_connsp_2(X35,X33,X34)|m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.19/0.38  fof(c_0_15, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.38  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_18, plain, ![X12, X13]:(~l1_pre_topc(X12)|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|r1_tarski(k1_tops_1(X12,X13),X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.19/0.38  cnf(c_0_19, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_20, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_23, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_25, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_29, plain, ![X10, X11]:(~v2_pre_topc(X10)|~l1_pre_topc(X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|v3_pre_topc(k1_tops_1(X10,X11),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk4_0))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(k1_tops_1(esk4_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_17]), c_0_24])])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (~m1_connsp_2(esk6_0,esk4_0,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_pre_topc(X1,esk4_0)|~r1_tarski(X1,esk6_0)|~r2_hidden(esk5_0,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (r1_tarski(esk7_0,esk6_0)|m1_connsp_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(esk5_0,k1_tops_1(esk4_0,X1))|~m1_connsp_2(X1,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_24]), c_0_27])]), c_0_28])).
% 0.19/0.38  cnf(c_0_35, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (r1_tarski(k1_tops_1(esk4_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (r1_tarski(esk7_0,esk6_0)|~r2_hidden(esk5_0,X1)|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk5_0,k1_tops_1(esk4_0,esk6_0))|r1_tarski(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_33])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (v3_pre_topc(k1_tops_1(esk4_0,esk6_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_17]), c_0_24]), c_0_27])])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (m1_subset_1(k1_tops_1(esk4_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.38  fof(c_0_42, plain, ![X17, X18, X19, X20]:((~v3_pre_topc(X20,X18)|k1_tops_1(X18,X20)=X20|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X18)|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(k1_tops_1(X17,X19)!=X19|v3_pre_topc(X19,X17)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X18)|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (r1_tarski(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_31])])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)|m1_connsp_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_45, plain, ![X14, X15, X16]:(~l1_pre_topc(X14)|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(~r1_tarski(X15,X16)|r1_tarski(k1_tops_1(X14,X15),k1_tops_1(X14,X16)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.19/0.38  cnf(c_0_46, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (r1_tarski(esk7_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_43])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)|~r2_hidden(esk5_0,X1)|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_32, c_0_44])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk5_0,k1_tops_1(esk4_0,esk6_0))|v3_pre_topc(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_44])).
% 0.19/0.38  fof(c_0_50, plain, ![X21, X22, X23, X25, X26, X28]:((((((m1_subset_1(esk1_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))|~r2_hidden(X23,X22)|~v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(v3_pre_topc(esk1_3(X21,X22,X23),X21)|~r2_hidden(X23,X22)|~v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(r1_tarski(esk1_3(X21,X22,X23),X22)|~r2_hidden(X23,X22)|~v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(r2_hidden(X23,esk1_3(X21,X22,X23))|~r2_hidden(X23,X22)|~v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X21)))|~v3_pre_topc(X26,X21)|~r1_tarski(X26,X22)|~r2_hidden(X25,X26)|r2_hidden(X25,X22)|~v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21))))&((~r2_hidden(esk2_2(X21,X22),X22)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X21)))|~v3_pre_topc(X28,X21)|~r1_tarski(X28,X22)|~r2_hidden(esk2_2(X21,X22),X28))|v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))&((((m1_subset_1(esk3_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))|r2_hidden(esk2_2(X21,X22),X22)|v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(v3_pre_topc(esk3_2(X21,X22),X21)|r2_hidden(esk2_2(X21,X22),X22)|v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(r1_tarski(esk3_2(X21,X22),X22)|r2_hidden(esk2_2(X21,X22),X22)|v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(r2_hidden(esk2_2(X21,X22),esk3_2(X21,X22))|r2_hidden(esk2_2(X21,X22),X22)|v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_tops_1])])])])])])).
% 0.19/0.38  cnf(c_0_51, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_17]), c_0_24]), c_0_27])])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_36, c_0_47])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_40]), c_0_41]), c_0_31])])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|m1_connsp_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_56, plain, (r2_hidden(X4,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r1_tarski(X1,X3)|~r2_hidden(X4,X1)|~v3_pre_topc(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_tops_1(esk4_0,X1),k1_tops_1(esk4_0,esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_17]), c_0_24])])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (k1_tops_1(esk4_0,esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_24])])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk5_0,X1)|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_32, c_0_55])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk4_0,esk6_0))|~r2_hidden(X1,X2)|~v3_pre_topc(X2,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X2,k1_tops_1(esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_41]), c_0_40]), c_0_24]), c_0_27])])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (r1_tarski(esk7_0,k1_tops_1(esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_43]), c_0_58]), c_0_53])])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk5_0,k1_tops_1(esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_40]), c_0_41]), c_0_31])])).
% 0.19/0.38  cnf(c_0_63, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk4_0,esk6_0))|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_54]), c_0_53]), c_0_61])])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_55]), c_0_62])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (m1_connsp_2(X1,esk4_0,esk5_0)|~r2_hidden(esk5_0,k1_tops_1(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_26]), c_0_24]), c_0_27])]), c_0_28])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (r2_hidden(esk5_0,k1_tops_1(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (m1_connsp_2(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_17])])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (~r2_hidden(esk5_0,X1)|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_68])])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_65]), c_0_54]), c_0_53]), c_0_43])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 71
% 0.19/0.38  # Proof object clause steps            : 50
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 41
% 0.19/0.38  # Proof object clause conjectures      : 38
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 20
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 28
% 0.19/0.38  # Proof object simplifying inferences  : 52
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 31
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 31
% 0.19/0.38  # Processed clauses                    : 159
% 0.19/0.38  # ...of these trivial                  : 8
% 0.19/0.38  # ...subsumed                          : 6
% 0.19/0.38  # ...remaining for further processing  : 145
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 23
% 0.19/0.38  # Generated clauses                    : 271
% 0.19/0.38  # ...of the previous two non-trivial   : 198
% 0.19/0.38  # Contextual simplify-reflections      : 5
% 0.19/0.38  # Paramodulations                      : 271
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 121
% 0.19/0.38  #    Positive orientable unit clauses  : 46
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 74
% 0.19/0.38  # Current number of unprocessed clauses: 57
% 0.19/0.38  # ...number of literals in the above   : 201
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 24
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 533
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 266
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.19/0.38  # Unit Clause-clause subsumption calls : 18
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 13
% 0.19/0.38  # BW rewrite match successes           : 9
% 0.19/0.38  # Condensation attempts                : 159
% 0.19/0.38  # Condensation successes               : 1
% 0.19/0.38  # Termbank termtop insertions          : 9422
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.039 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.042 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
