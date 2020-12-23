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
% DateTime   : Thu Dec  3 11:14:23 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 204 expanded)
%              Number of clauses        :   39 (  72 expanded)
%              Number of leaves         :   11 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  243 (1404 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   14 (   3 average)
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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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

fof(t6_connsp_2,axiom,(
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_13,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | m1_subset_1(k1_tops_1(X21,X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_14,negated_conjecture,(
    ! [X37] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & m1_connsp_2(esk4_0,esk2_0,esk3_0)
      & ( v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ m1_connsp_2(X37,esk2_0,esk3_0)
        | ~ v3_pre_topc(X37,esk2_0)
        | ~ r1_tarski(X37,esk4_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

fof(c_0_15,plain,(
    ! [X28,X29,X30] :
      ( v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | ~ v3_pre_topc(X29,X28)
      | ~ r2_hidden(X30,X29)
      | m1_connsp_2(X29,X28,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_16,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | m1_subset_1(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X23,X24] :
      ( ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | v3_pre_topc(k1_tops_1(X23,X24),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_24,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | ~ v1_xboole_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X25,X26,X27] :
      ( ( ~ m1_connsp_2(X27,X25,X26)
        | r2_hidden(X26,k1_tops_1(X25,X27))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ r2_hidden(X26,k1_tops_1(X25,X27))
        | m1_connsp_2(X27,X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_39,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | ~ m1_connsp_2(X32,X31,X33)
      | r2_hidden(X33,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).

cnf(c_0_40,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_28])).

fof(c_0_42,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_43,plain,
    ( m1_connsp_2(k1_tops_1(X1,X2),X1,X3)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,k1_tops_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_19])).

cnf(c_0_44,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_20]),c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_connsp_2(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_35]),c_0_20])]),c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_connsp_2(X1,esk2_0,esk3_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( m1_connsp_2(k1_tops_1(esk2_0,esk4_0),esk2_0,X1)
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_36]),c_0_35]),c_0_20])]),c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(k1_tops_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_35]),c_0_20]),c_0_36])]),c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk1_2(k1_tops_1(esk2_0,esk4_0),X1),u1_struct_0(esk2_0))
    | r1_tarski(k1_tops_1(esk2_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( ~ v3_pre_topc(k1_tops_1(esk2_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_45])]),c_0_52])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_2(k1_tops_1(esk2_0,esk4_0),X1),esk4_0)
    | r1_tarski(k1_tops_1(esk2_0,esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_49]),c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_30]),c_0_35]),c_0_20]),c_0_36])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_28]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:15:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.20/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.028 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t7_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X3,X1,X2)&![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))=>~(((m1_connsp_2(X4,X1,X2)&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 0.20/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.37  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.20/0.37  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.20/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.37  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.20/0.37  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.37  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.20/0.37  fof(t6_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(m1_connsp_2(X2,X1,X3)=>r2_hidden(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 0.20/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.37  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X3,X1,X2)&![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))=>~(((m1_connsp_2(X4,X1,X2)&v3_pre_topc(X4,X1))&r1_tarski(X4,X3)))))))))), inference(assume_negation,[status(cth)],[t7_connsp_2])).
% 0.20/0.37  fof(c_0_12, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.37  fof(c_0_13, plain, ![X21, X22]:(~l1_pre_topc(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|m1_subset_1(k1_tops_1(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.20/0.37  fof(c_0_14, negated_conjecture, ![X37]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_connsp_2(esk4_0,esk2_0,esk3_0)&(v1_xboole_0(X37)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk2_0)))|(~m1_connsp_2(X37,esk2_0,esk3_0)|~v3_pre_topc(X37,esk2_0)|~r1_tarski(X37,esk4_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.20/0.37  fof(c_0_15, plain, ![X28, X29, X30]:(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|(~m1_subset_1(X30,u1_struct_0(X28))|(~v3_pre_topc(X29,X28)|~r2_hidden(X30,X29)|m1_connsp_2(X29,X28,X30))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.20/0.37  fof(c_0_16, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|m1_subset_1(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.37  fof(c_0_17, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.37  cnf(c_0_18, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_19, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_21, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_22, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  fof(c_0_23, plain, ![X23, X24]:(~v2_pre_topc(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|v3_pre_topc(k1_tops_1(X23,X24),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.20/0.37  fof(c_0_24, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|~v1_xboole_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.37  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.37  fof(c_0_27, plain, ![X25, X26, X27]:((~m1_connsp_2(X27,X25,X26)|r2_hidden(X26,k1_tops_1(X25,X27))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|~m1_subset_1(X26,u1_struct_0(X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(~r2_hidden(X26,k1_tops_1(X25,X27))|m1_connsp_2(X27,X25,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|~m1_subset_1(X26,u1_struct_0(X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.20/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.37  cnf(c_0_29, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)), inference(csr,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.37  cnf(c_0_30, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.37  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.37  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.37  cnf(c_0_33, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.37  cnf(c_0_34, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_35, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_38, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  fof(c_0_39, plain, ![X31, X32, X33]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(~m1_subset_1(X33,u1_struct_0(X31))|(~m1_connsp_2(X32,X31,X33)|r2_hidden(X33,X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).
% 0.20/0.37  cnf(c_0_40, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.37  cnf(c_0_41, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X1,k1_tops_1(esk2_0,X2))), inference(spm,[status(thm)],[c_0_22, c_0_28])).
% 0.20/0.37  fof(c_0_42, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.37  cnf(c_0_43, plain, (m1_connsp_2(k1_tops_1(X1,X2),X1,X3)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,k1_tops_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_19])).
% 0.20/0.37  cnf(c_0_44, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.37  cnf(c_0_45, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_20]), c_0_36]), c_0_37])]), c_0_38])).
% 0.20/0.37  cnf(c_0_46, plain, (v2_struct_0(X1)|r2_hidden(X3,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_connsp_2(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.37  cnf(c_0_47, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k1_tops_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_35]), c_0_20])]), c_0_38])).
% 0.20/0.37  cnf(c_0_48, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k1_tops_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_36])).
% 0.20/0.37  cnf(c_0_49, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.37  cnf(c_0_50, negated_conjecture, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_connsp_2(X1,esk2_0,esk3_0)|~v3_pre_topc(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_51, negated_conjecture, (m1_connsp_2(k1_tops_1(esk2_0,esk4_0),esk2_0,X1)|~r2_hidden(X1,k1_tops_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_36]), c_0_35]), c_0_20])]), c_0_38])).
% 0.20/0.37  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(k1_tops_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.37  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k1_tops_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_35]), c_0_20]), c_0_36])]), c_0_38])).
% 0.20/0.37  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk1_2(k1_tops_1(esk2_0,esk4_0),X1),u1_struct_0(esk2_0))|r1_tarski(k1_tops_1(esk2_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.37  cnf(c_0_55, negated_conjecture, (~v3_pre_topc(k1_tops_1(esk2_0,esk4_0),esk2_0)|~m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_45])]), c_0_52])).
% 0.20/0.38  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_2(k1_tops_1(esk2_0,esk4_0),X1),esk4_0)|r1_tarski(k1_tops_1(esk2_0,esk4_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_49]), c_0_54])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (~m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_30]), c_0_35]), c_0_20]), c_0_36])])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (~m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_28]), c_0_36])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 62
% 0.20/0.38  # Proof object clause steps            : 39
% 0.20/0.38  # Proof object formula steps           : 23
% 0.20/0.38  # Proof object conjectures             : 25
% 0.20/0.38  # Proof object clause conjectures      : 22
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 19
% 0.20/0.38  # Proof object initial formulas used   : 11
% 0.20/0.38  # Proof object generating inferences   : 17
% 0.20/0.38  # Proof object simplifying inferences  : 34
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 11
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 23
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 23
% 0.20/0.38  # Processed clauses                    : 134
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 23
% 0.20/0.38  # ...remaining for further processing  : 110
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 2
% 0.20/0.38  # Generated clauses                    : 135
% 0.20/0.38  # ...of the previous two non-trivial   : 125
% 0.20/0.38  # Contextual simplify-reflections      : 3
% 0.20/0.38  # Paramodulations                      : 133
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 83
% 0.20/0.38  #    Positive orientable unit clauses  : 13
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 6
% 0.20/0.38  #    Non-unit-clauses                  : 64
% 0.20/0.38  # Current number of unprocessed clauses: 35
% 0.20/0.38  # ...number of literals in the above   : 122
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 25
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 608
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 311
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 15
% 0.20/0.38  # Unit Clause-clause subsumption calls : 66
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 15
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 4704
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.035 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.040 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
