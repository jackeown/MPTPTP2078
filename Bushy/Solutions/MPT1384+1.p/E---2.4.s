%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : connsp_2__t9_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:54 EDT 2019

% Result     : Theorem 13.34s
% Output     : CNFRefutation 13.34s
% Verified   : 
% Statistics : Number of formulae       :  101 (1396 expanded)
%              Number of clauses        :   76 ( 517 expanded)
%              Number of leaves         :   12 ( 350 expanded)
%              Depth                    :   15
%              Number of atoms          :  563 (13511 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   66 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( m1_connsp_2(X4,X1,X3)
                            & r1_tarski(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t9_connsp_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t1_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t5_connsp_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t4_subset)).

fof(t8_connsp_2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t8_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',dt_m1_connsp_2)).

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
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t57_tops_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t5_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t7_boole)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t1_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t2_subset)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ ( r2_hidden(X3,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( m1_connsp_2(X4,X1,X3)
                              & r1_tarski(X4,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_connsp_2])).

fof(c_0_13,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_14,negated_conjecture,(
    ! [X8,X9] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
        | ~ v3_pre_topc(esk2_0,esk1_0) )
      & ( r2_hidden(esk3_0,esk2_0)
        | ~ v3_pre_topc(esk2_0,esk1_0) )
      & ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ m1_connsp_2(X8,esk1_0,esk3_0)
        | ~ r1_tarski(X8,esk2_0)
        | ~ v3_pre_topc(esk2_0,esk1_0) )
      & ( m1_subset_1(esk4_1(X9),k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r2_hidden(X9,esk2_0)
        | ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | v3_pre_topc(esk2_0,esk1_0) )
      & ( m1_connsp_2(esk4_1(X9),esk1_0,X9)
        | ~ r2_hidden(X9,esk2_0)
        | ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | v3_pre_topc(esk2_0,esk1_0) )
      & ( r1_tarski(esk4_1(X9),esk2_0)
        | ~ r2_hidden(X9,esk2_0)
        | ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | v3_pre_topc(esk2_0,esk1_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

fof(c_0_15,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(X26,X27)
      | ~ r1_tarski(X27,X28)
      | r1_tarski(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X45,X46,X47] :
      ( v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
      | ~ m1_subset_1(X47,u1_struct_0(X45))
      | ~ v3_pre_topc(X46,X45)
      | ~ r2_hidden(X47,X46)
      | m1_connsp_2(X46,X45,X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_19,plain,(
    ! [X33,X34,X35] :
      ( ~ r2_hidden(X33,X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X35))
      | m1_subset_1(X33,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_20,plain,(
    ! [X56,X57,X58,X60] :
      ( ( m1_subset_1(esk12_3(X56,X57,X58),k1_zfmisc_1(u1_struct_0(X56)))
        | ~ m1_connsp_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ m1_subset_1(X57,u1_struct_0(X56))
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( v3_pre_topc(esk12_3(X56,X57,X58),X56)
        | ~ m1_connsp_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ m1_subset_1(X57,u1_struct_0(X56))
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( r1_tarski(esk12_3(X56,X57,X58),X58)
        | ~ m1_connsp_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ m1_subset_1(X57,u1_struct_0(X56))
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( r2_hidden(X57,esk12_3(X56,X57,X58))
        | ~ m1_connsp_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ m1_subset_1(X57,u1_struct_0(X56))
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ v3_pre_topc(X60,X56)
        | ~ r1_tarski(X60,X58)
        | ~ r2_hidden(X57,X60)
        | m1_connsp_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ m1_subset_1(X57,u1_struct_0(X56))
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_connsp_2])])])])])])).

fof(c_0_21,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_connsp_2(X16,X14,X15)
      | m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk12_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v3_pre_topc(esk12_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_connsp_2(X1,esk1_0,esk3_0)
    | ~ r1_tarski(X1,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X3,X1)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk12_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( v3_pre_topc(esk12_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_35,plain,
    ( m1_connsp_2(X3,X2,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(X1,esk2_0)
    | ~ m1_connsp_2(X1,esk1_0,esk3_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_37,plain,
    ( m1_connsp_2(esk12_3(X1,X2,X3),X1,X4)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ r2_hidden(X4,esk12_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,plain,
    ( r1_tarski(esk12_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r1_tarski(X4,X1)
    | ~ r2_hidden(X3,X4)
    | ~ v3_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_35,c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(esk12_3(esk1_0,X1,X2),esk2_0)
    | ~ m1_connsp_2(X2,esk1_0,X1)
    | ~ r2_hidden(esk3_0,esk12_3(esk1_0,X1,X2))
    | ~ v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_44,plain,
    ( r1_tarski(esk12_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,esk12_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_46,plain,(
    ! [X36,X37,X38,X40,X41,X43] :
      ( ( m1_subset_1(esk9_3(X36,X37,X38),k1_zfmisc_1(u1_struct_0(X36)))
        | ~ r2_hidden(X38,X37)
        | ~ v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( v3_pre_topc(esk9_3(X36,X37,X38),X36)
        | ~ r2_hidden(X38,X37)
        | ~ v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( r1_tarski(esk9_3(X36,X37,X38),X37)
        | ~ r2_hidden(X38,X37)
        | ~ v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( r2_hidden(X38,esk9_3(X36,X37,X38))
        | ~ r2_hidden(X38,X37)
        | ~ v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v3_pre_topc(X41,X36)
        | ~ r1_tarski(X41,X37)
        | ~ r2_hidden(X40,X41)
        | r2_hidden(X40,X37)
        | ~ v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ r2_hidden(esk10_2(X36,X37),X37)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v3_pre_topc(X43,X36)
        | ~ r1_tarski(X43,X37)
        | ~ r2_hidden(esk10_2(X36,X37),X43)
        | v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( m1_subset_1(esk11_2(X36,X37),k1_zfmisc_1(u1_struct_0(X36)))
        | r2_hidden(esk10_2(X36,X37),X37)
        | v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( v3_pre_topc(esk11_2(X36,X37),X36)
        | r2_hidden(esk10_2(X36,X37),X37)
        | v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( r1_tarski(esk11_2(X36,X37),X37)
        | r2_hidden(esk10_2(X36,X37),X37)
        | v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( r2_hidden(esk10_2(X36,X37),esk11_2(X36,X37))
        | r2_hidden(esk10_2(X36,X37),X37)
        | v3_pre_topc(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_tops_1])])])])])])).

cnf(c_0_47,negated_conjecture,
    ( m1_connsp_2(esk2_0,esk1_0,X1)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_17]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk4_1(X1),esk2_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( ~ m1_connsp_2(esk2_0,esk1_0,X1)
    | ~ r2_hidden(esk3_0,esk12_3(esk1_0,X1,esk2_0))
    | ~ v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,esk12_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_45,c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,plain,
    ( v3_pre_topc(esk11_2(X1,X2),X1)
    | r2_hidden(esk10_2(X1,X2),X2)
    | v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_54,plain,(
    ! [X48,X49,X50] :
      ( ~ r2_hidden(X48,X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(X50))
      | ~ v1_xboole_0(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_55,negated_conjecture,
    ( m1_connsp_2(esk2_0,esk1_0,X1)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_30]),c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ r1_tarski(X1,esk4_1(X2))
    | ~ r2_hidden(X2,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_48]),c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_connsp_2(esk2_0,esk1_0,esk3_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_38]),c_0_39])]),c_0_40]),c_0_52])).

cnf(c_0_58,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r1_tarski(X1,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk11_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(esk10_2(X1,X2),X2)
    | v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk10_2(esk1_0,esk2_0),esk2_0)
    | v3_pre_topc(esk11_2(esk1_0,esk2_0),esk1_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_17]),c_0_38]),c_0_39])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( v3_pre_topc(X2,X1)
    | ~ r2_hidden(esk10_2(X1,X2),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(esk10_2(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_64,negated_conjecture,
    ( m1_connsp_2(esk2_0,esk1_0,X1)
    | ~ r1_tarski(esk12_3(esk1_0,X2,X3),esk2_0)
    | ~ m1_connsp_2(X3,esk1_0,X2)
    | ~ r2_hidden(X1,esk12_3(esk1_0,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_34]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk12_3(X1,X2,esk4_1(X3)),esk2_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(esk4_1(X3),X1,X2)
    | ~ r2_hidden(X3,esk2_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_44])).

cnf(c_0_66,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_23]),c_0_38]),c_0_39])]),c_0_40]),c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk10_2(esk1_0,esk2_0),esk2_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | m1_subset_1(esk11_2(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_17]),c_0_38]),c_0_39])])).

cnf(c_0_68,negated_conjecture,
    ( m1_connsp_2(esk2_0,esk1_0,X1)
    | r2_hidden(esk10_2(esk1_0,esk2_0),esk2_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ r1_tarski(esk11_2(esk1_0,esk2_0),esk2_0)
    | ~ r2_hidden(X1,esk11_2(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_61])).

cnf(c_0_69,plain,
    ( r1_tarski(esk11_2(X1,X2),X2)
    | r2_hidden(esk10_2(X1,X2),X2)
    | v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_70,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_30])).

cnf(c_0_71,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X3)
    | ~ r1_tarski(esk12_3(X3,esk10_2(X2,X1),X4),X1)
    | ~ m1_connsp_2(X4,X3,esk10_2(X2,X1))
    | ~ r2_hidden(esk10_2(X2,X1),X1)
    | ~ v3_pre_topc(esk12_3(X3,esk10_2(X2,X1),X4),X2)
    | ~ m1_subset_1(esk12_3(X3,esk10_2(X2,X1),X4),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(esk10_2(X2,X1),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_51])).

cnf(c_0_72,negated_conjecture,
    ( m1_connsp_2(esk2_0,esk1_0,X1)
    | ~ m1_connsp_2(esk4_1(X2),esk1_0,X3)
    | ~ r2_hidden(X1,esk12_3(esk1_0,X3,esk4_1(X2)))
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_38]),c_0_39])]),c_0_66]),c_0_40])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk10_2(esk1_0,esk2_0),esk2_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk11_2(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_67])).

cnf(c_0_74,plain,
    ( r2_hidden(esk10_2(X1,X2),esk11_2(X1,X2))
    | r2_hidden(esk10_2(X1,X2),X2)
    | v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_30])).

cnf(c_0_76,negated_conjecture,
    ( m1_connsp_2(esk2_0,esk1_0,X1)
    | r2_hidden(esk10_2(esk1_0,esk2_0),esk2_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ r2_hidden(X1,esk11_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_17]),c_0_38]),c_0_39])])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_connsp_2(X2,X1,X3)
    | ~ r2_hidden(X4,esk12_3(X1,X3,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_44])).

fof(c_0_78,plain,(
    ! [X52,X53] :
      ( ~ r2_hidden(X52,X53)
      | ~ v1_xboole_0(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_79,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r1_tarski(esk12_3(X2,esk10_2(X2,X1),X3),X1)
    | ~ m1_connsp_2(X3,X2,esk10_2(X2,X1))
    | ~ r2_hidden(esk10_2(X2,X1),X1)
    | ~ v3_pre_topc(esk12_3(X2,esk10_2(X2,X1),X3),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_33]),c_0_25])).

cnf(c_0_80,negated_conjecture,
    ( m1_connsp_2(esk2_0,esk1_0,X1)
    | ~ m1_connsp_2(esk4_1(X2),esk1_0,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_51]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_81,negated_conjecture,
    ( m1_connsp_2(esk4_1(X1),esk1_0,X1)
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_82,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | m1_subset_1(esk10_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_17]),c_0_38]),c_0_39])]),c_0_49])).

cnf(c_0_83,plain,
    ( m1_subset_1(X1,X2)
    | v2_struct_0(X3)
    | ~ m1_connsp_2(X2,X3,X4)
    | ~ r2_hidden(X1,esk12_3(X3,X4,X2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_75,c_0_44])).

cnf(c_0_84,negated_conjecture,
    ( m1_connsp_2(esk2_0,esk1_0,esk10_2(esk1_0,esk2_0))
    | r2_hidden(esk10_2(esk1_0,esk2_0),esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_74]),c_0_17]),c_0_38]),c_0_39])])).

fof(c_0_85,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | m1_subset_1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_86,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_connsp_2(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_51])).

cnf(c_0_87,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_88,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,esk10_2(X2,X1))
    | ~ r2_hidden(esk10_2(X2,X1),X1)
    | ~ m1_subset_1(esk10_2(X2,X1),u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_44]),c_0_27]),c_0_34])).

cnf(c_0_89,negated_conjecture,
    ( m1_connsp_2(esk2_0,esk1_0,X1)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_66]),c_0_49])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk10_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_82,c_0_66])).

fof(c_0_91,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X29,X30)
      | v1_xboole_0(X30)
      | r2_hidden(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_92,plain,
    ( m1_subset_1(X1,X2)
    | v2_struct_0(X3)
    | ~ m1_connsp_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_83,c_0_51])).

cnf(c_0_93,negated_conjecture,
    ( m1_connsp_2(esk2_0,esk1_0,esk10_2(esk1_0,esk2_0))
    | r2_hidden(esk10_2(esk1_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[c_0_84,c_0_66])).

cnf(c_0_94,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_84]),c_0_38]),c_0_39])]),c_0_40]),c_0_82]),c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( ~ r2_hidden(esk10_2(esk1_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_38]),c_0_39])]),c_0_66]),c_0_40])).

cnf(c_0_97,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(esk10_2(esk1_0,esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_90]),c_0_38]),c_0_39])]),c_0_40]),c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_95]),c_0_87])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])]),c_0_99]),
    [proof]).
%------------------------------------------------------------------------------
