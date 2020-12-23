%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:20 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 438 expanded)
%              Number of clauses        :   57 ( 189 expanded)
%              Number of leaves         :    8 ( 105 expanded)
%              Depth                    :   19
%              Number of atoms          :  254 (2273 expanded)
%              Number of equality atoms :   13 (  83 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( m1_connsp_2(X3,X1,X2)
                      & m1_connsp_2(X4,X1,X2) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X1),X3,X4),X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_connsp_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

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

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( m1_connsp_2(X3,X1,X2)
                        & m1_connsp_2(X4,X1,X2) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X1),X3,X4),X1,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_connsp_2])).

fof(c_0_9,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_connsp_2(esk5_0,esk3_0,esk4_0)
    & m1_connsp_2(esk6_0,esk3_0,esk4_0)
    & ~ m1_connsp_2(k4_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0),esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X18)
        | r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X25,X26,X27] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ r1_tarski(X26,X27)
      | r1_tarski(k1_tops_1(X25,X26),k1_tops_1(X25,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X2)
    | r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk6_0,X1),X2),u1_struct_0(esk3_0))
    | r2_hidden(esk1_2(k2_xboole_0(esk6_0,X1),X2),X1)
    | r1_tarski(k2_xboole_0(esk6_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,u1_struct_0(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk6_0,esk5_0),X1),u1_struct_0(esk3_0))
    | r1_tarski(k2_xboole_0(esk6_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_36,plain,(
    ! [X28,X29,X30] :
      ( ( ~ m1_connsp_2(X30,X28,X29)
        | r2_hidden(X29,k1_tops_1(X28,X30))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ r2_hidden(X29,k1_tops_1(X28,X30))
        | m1_connsp_2(X30,X28,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk5_0),k1_tops_1(esk3_0,X1))
    | ~ r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_16]),c_0_33])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk6_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_34])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_40,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk5_0),k1_tops_1(esk3_0,k2_xboole_0(esk6_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

fof(c_0_42,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_connsp_2(X33,X31,X32)
      | m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_43,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ r2_hidden(X3,k1_tops_1(X2,X1))
    | ~ r1_tarski(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,k2_xboole_0(esk6_0,esk5_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( m1_connsp_2(k2_xboole_0(esk6_0,esk5_0),esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_33]),c_0_38])]),c_0_46])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( m1_connsp_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk6_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_45]),c_0_33])]),c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk4_0,k1_tops_1(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_45]),c_0_33]),c_0_52])]),c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk5_0,X1),X2),u1_struct_0(esk3_0))
    | r2_hidden(esk1_2(k2_xboole_0(esk5_0,X1),X2),X1)
    | r1_tarski(k2_xboole_0(esk5_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk6_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_52])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk5_0,esk6_0),X1),u1_struct_0(esk3_0))
    | r1_tarski(k2_xboole_0(esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_56])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_57])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_2(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)),X2)
    | r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_24])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,k2_xboole_0(esk6_0,esk5_0)),k1_tops_1(esk3_0,X1))
    | ~ r1_tarski(k2_xboole_0(esk6_0,esk5_0),X1)
    | ~ r1_tarski(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_58]),c_0_33])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_59])).

cnf(c_0_64,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,k2_xboole_0(esk6_0,esk5_0)),k1_tops_1(esk3_0,k2_xboole_0(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

fof(c_0_66,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | k4_subset_1(X20,X21,X22) = k2_xboole_0(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,k2_xboole_0(esk5_0,esk6_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,k2_xboole_0(esk6_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0),esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_69,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,k2_xboole_0(esk5_0,esk6_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_44])).

cnf(c_0_71,negated_conjecture,
    ( ~ m1_connsp_2(k2_xboole_0(esk5_0,esk6_0),esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_14]),c_0_16])])).

cnf(c_0_72,negated_conjecture,
    ( m1_connsp_2(k2_xboole_0(esk5_0,esk6_0),esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_70]),c_0_45]),c_0_33]),c_0_63])]),c_0_46])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_52]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:16:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.52  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.028 s
% 0.19/0.52  # Presaturation interreduction done
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t3_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((m1_connsp_2(X3,X1,X2)&m1_connsp_2(X4,X1,X2))=>m1_connsp_2(k4_subset_1(u1_struct_0(X1),X3,X4),X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_connsp_2)).
% 0.19/0.52  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.52  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.52  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.19/0.52  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.19/0.52  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.19/0.52  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.19/0.52  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((m1_connsp_2(X3,X1,X2)&m1_connsp_2(X4,X1,X2))=>m1_connsp_2(k4_subset_1(u1_struct_0(X1),X3,X4),X1,X2))))))), inference(assume_negation,[status(cth)],[t3_connsp_2])).
% 0.19/0.52  fof(c_0_9, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.52  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((m1_connsp_2(esk5_0,esk3_0,esk4_0)&m1_connsp_2(esk6_0,esk3_0,esk4_0))&~m1_connsp_2(k4_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0),esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.19/0.52  fof(c_0_11, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk2_3(X16,X17,X18),X18)|(r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.52  fof(c_0_12, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.52  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.52  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_15, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.52  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.52  cnf(c_0_18, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.52  cnf(c_0_19, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.52  fof(c_0_21, plain, ![X25, X26, X27]:(~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|(~r1_tarski(X26,X27)|r1_tarski(k1_tops_1(X25,X26),k1_tops_1(X25,X27)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.19/0.52  cnf(c_0_22, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_13, c_0_16])).
% 0.19/0.52  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.52  cnf(c_0_24, plain, (r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X2)|r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X1)|r1_tarski(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.52  cnf(c_0_25, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.52  cnf(c_0_26, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.52  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.52  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 0.19/0.52  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk6_0,X1),X2),u1_struct_0(esk3_0))|r2_hidden(esk1_2(k2_xboole_0(esk6_0,X1),X2),X1)|r1_tarski(k2_xboole_0(esk6_0,X1),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.52  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.52  cnf(c_0_31, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.52  cnf(c_0_32, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,u1_struct_0(X1))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.52  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk6_0,esk5_0),X1),u1_struct_0(esk3_0))|r1_tarski(k2_xboole_0(esk6_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.52  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.52  fof(c_0_36, plain, ![X28, X29, X30]:((~m1_connsp_2(X30,X28,X29)|r2_hidden(X29,k1_tops_1(X28,X30))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(~r2_hidden(X29,k1_tops_1(X28,X30))|m1_connsp_2(X30,X28,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.19/0.52  cnf(c_0_37, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk5_0),k1_tops_1(esk3_0,X1))|~r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_16]), c_0_33])])).
% 0.19/0.52  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_xboole_0(esk6_0,esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_34])).
% 0.19/0.52  cnf(c_0_39, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_35, c_0_20])).
% 0.19/0.52  cnf(c_0_40, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.52  cnf(c_0_41, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk5_0),k1_tops_1(esk3_0,k2_xboole_0(esk6_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.19/0.52  fof(c_0_42, plain, ![X31, X32, X33]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,u1_struct_0(X31))|(~m1_connsp_2(X33,X31,X32)|m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.19/0.52  cnf(c_0_43, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~r2_hidden(X3,k1_tops_1(X2,X1))|~r1_tarski(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_40, c_0_27])).
% 0.19/0.52  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,k2_xboole_0(esk6_0,esk5_0)))|~r2_hidden(X1,k1_tops_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_17, c_0_41])).
% 0.19/0.52  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_46, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_47, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.52  cnf(c_0_48, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.52  cnf(c_0_49, negated_conjecture, (m1_connsp_2(k2_xboole_0(esk6_0,esk5_0),esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k1_tops_1(esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_33]), c_0_38])]), c_0_46])).
% 0.19/0.52  cnf(c_0_50, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.52  cnf(c_0_51, negated_conjecture, (m1_connsp_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_53, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.52  cnf(c_0_54, negated_conjecture, (m1_subset_1(k2_xboole_0(esk6_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k1_tops_1(esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_45]), c_0_33])]), c_0_46])).
% 0.19/0.52  cnf(c_0_55, negated_conjecture, (r2_hidden(esk4_0,k1_tops_1(esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_45]), c_0_33]), c_0_52])]), c_0_46])).
% 0.19/0.52  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk5_0,X1),X2),u1_struct_0(esk3_0))|r2_hidden(esk1_2(k2_xboole_0(esk5_0,X1),X2),X1)|r1_tarski(k2_xboole_0(esk5_0,X1),X2)), inference(spm,[status(thm)],[c_0_28, c_0_24])).
% 0.19/0.52  cnf(c_0_57, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_53])).
% 0.19/0.52  cnf(c_0_58, negated_conjecture, (m1_subset_1(k2_xboole_0(esk6_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_52])])).
% 0.19/0.52  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk5_0,esk6_0),X1),u1_struct_0(esk3_0))|r1_tarski(k2_xboole_0(esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_23, c_0_56])).
% 0.19/0.52  cnf(c_0_60, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_30, c_0_57])).
% 0.19/0.52  cnf(c_0_61, plain, (r2_hidden(esk1_2(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)),X2)|r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_35, c_0_24])).
% 0.19/0.52  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,k2_xboole_0(esk6_0,esk5_0)),k1_tops_1(esk3_0,X1))|~r1_tarski(k2_xboole_0(esk6_0,esk5_0),X1)|~r1_tarski(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_58]), c_0_33])])).
% 0.19/0.52  cnf(c_0_63, negated_conjecture, (r1_tarski(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_59])).
% 0.19/0.52  cnf(c_0_64, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.52  cnf(c_0_65, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,k2_xboole_0(esk6_0,esk5_0)),k1_tops_1(esk3_0,k2_xboole_0(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.19/0.52  fof(c_0_66, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|~m1_subset_1(X22,k1_zfmisc_1(X20))|k4_subset_1(X20,X21,X22)=k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.19/0.52  cnf(c_0_67, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,k2_xboole_0(esk5_0,esk6_0)))|~r2_hidden(X1,k1_tops_1(esk3_0,k2_xboole_0(esk6_0,esk5_0)))), inference(spm,[status(thm)],[c_0_17, c_0_65])).
% 0.19/0.52  cnf(c_0_68, negated_conjecture, (~m1_connsp_2(k4_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0),esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_69, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.52  cnf(c_0_70, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,k2_xboole_0(esk5_0,esk6_0)))|~r2_hidden(X1,k1_tops_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_67, c_0_44])).
% 0.19/0.52  cnf(c_0_71, negated_conjecture, (~m1_connsp_2(k2_xboole_0(esk5_0,esk6_0),esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_14]), c_0_16])])).
% 0.19/0.52  cnf(c_0_72, negated_conjecture, (m1_connsp_2(k2_xboole_0(esk5_0,esk6_0),esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k1_tops_1(esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_70]), c_0_45]), c_0_33]), c_0_63])]), c_0_46])).
% 0.19/0.52  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_52]), c_0_55])]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 74
% 0.19/0.52  # Proof object clause steps            : 57
% 0.19/0.52  # Proof object formula steps           : 17
% 0.19/0.52  # Proof object conjectures             : 35
% 0.19/0.52  # Proof object clause conjectures      : 32
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 21
% 0.19/0.52  # Proof object initial formulas used   : 8
% 0.19/0.52  # Proof object generating inferences   : 32
% 0.19/0.52  # Proof object simplifying inferences  : 39
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 8
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 25
% 0.19/0.52  # Removed in clause preprocessing      : 0
% 0.19/0.52  # Initial clauses in saturation        : 25
% 0.19/0.52  # Processed clauses                    : 685
% 0.19/0.52  # ...of these trivial                  : 2
% 0.19/0.52  # ...subsumed                          : 211
% 0.19/0.52  # ...remaining for further processing  : 472
% 0.19/0.52  # Other redundant clauses eliminated   : 3
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 7
% 0.19/0.52  # Backward-rewritten                   : 14
% 0.19/0.52  # Generated clauses                    : 10784
% 0.19/0.52  # ...of the previous two non-trivial   : 10281
% 0.19/0.52  # Contextual simplify-reflections      : 3
% 0.19/0.52  # Paramodulations                      : 10545
% 0.19/0.52  # Factorizations                       : 236
% 0.19/0.52  # Equation resolutions                 : 3
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 423
% 0.19/0.52  #    Positive orientable unit clauses  : 139
% 0.19/0.52  #    Positive unorientable unit clauses: 0
% 0.19/0.52  #    Negative unit clauses             : 3
% 0.19/0.52  #    Non-unit-clauses                  : 281
% 0.19/0.52  # Current number of unprocessed clauses: 9630
% 0.19/0.52  # ...number of literals in the above   : 36890
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 46
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 13535
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 9489
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 220
% 0.19/0.52  # Unit Clause-clause subsumption calls : 641
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 263
% 0.19/0.52  # BW rewrite match successes           : 9
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 218872
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.179 s
% 0.19/0.52  # System time              : 0.007 s
% 0.19/0.52  # Total time               : 0.186 s
% 0.19/0.52  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
