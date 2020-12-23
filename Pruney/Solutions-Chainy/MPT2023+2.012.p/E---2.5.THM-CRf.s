%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:39 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 589 expanded)
%              Number of clauses        :   47 ( 201 expanded)
%              Number of leaves         :   10 ( 141 expanded)
%              Depth                    :   12
%              Number of atoms          :  272 (3376 expanded)
%              Number of equality atoms :   23 ( 112 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))
                 => m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).

fof(t38_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
             => ? [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                  & X4 = X3
                  & r2_hidden(X2,X4)
                  & v3_pre_topc(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

fof(t39_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))
              <=> ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(fc6_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v3_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v3_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k3_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))
                   => m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_waybel_9])).

fof(c_0_11,plain,(
    ! [X30,X31,X32] :
      ( ( m1_subset_1(esk2_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X32,u1_struct_0(k9_yellow_6(X30,X31)))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( esk2_3(X30,X31,X32) = X32
        | ~ m1_subset_1(X32,u1_struct_0(k9_yellow_6(X30,X31)))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( r2_hidden(X31,esk2_3(X30,X31,X32))
        | ~ m1_subset_1(X32,u1_struct_0(k9_yellow_6(X30,X31)))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( v3_pre_topc(esk2_3(X30,X31,X32),X30)
        | ~ m1_subset_1(X32,u1_struct_0(k9_yellow_6(X30,X31)))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))
    & m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))
    & ~ m1_subset_1(k3_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_13,plain,
    ( esk2_3(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X34,X35,X36] :
      ( ( r2_hidden(X35,X36)
        | ~ r2_hidden(X36,u1_struct_0(k9_yellow_6(X34,X35)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( v3_pre_topc(X36,X34)
        | ~ r2_hidden(X36,u1_struct_0(k9_yellow_6(X34,X35)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ r2_hidden(X35,X36)
        | ~ v3_pre_topc(X36,X34)
        | r2_hidden(X36,u1_struct_0(k9_yellow_6(X34,X35)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).

fof(c_0_19,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | m1_subset_1(X24,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_20,plain,(
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

fof(c_0_21,plain,(
    ! [X20,X21] : k1_setfam_1(k2_tarski(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_22,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k9_subset_1(X17,X18,X19) = k3_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,X1) = X1
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | m1_subset_1(k9_subset_1(X14,X15,X16),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X4)
    | X4 != k1_setfam_1(k2_tarski(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25])])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_struct_0(k9_yellow_6(X1,X4)))
    | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X4,k9_subset_1(u1_struct_0(X1),X2,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,esk6_0)) = k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_44,plain,(
    ! [X27,X28,X29] :
      ( ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ v3_pre_topc(X28,X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | ~ v3_pre_topc(X29,X27)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
      | v3_pre_topc(k3_xboole_0(X28,X29),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_tops_1])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,X2)))
    | ~ v3_pre_topc(k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0),esk3_0)
    | ~ r2_hidden(X2,k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,k9_subset_1(u1_struct_0(esk3_0),X2,esk6_0))
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_3(esk3_0,esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,esk5_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_43])).

cnf(c_0_49,plain,
    ( v3_pre_topc(k3_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,X2)))
    | ~ v3_pre_topc(k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0),esk3_0)
    | ~ r2_hidden(X2,esk6_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_43]),c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_25]),c_0_33])).

cnf(c_0_54,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(X2,X3)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk3_0,esk4_0,X1),esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( ~ m1_subset_1(k3_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_57,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | m1_subset_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))
    | ~ v3_pre_topc(k9_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_59,negated_conjecture,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0),X2)
    | ~ v3_pre_topc(esk6_0,X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_41])).

cnf(c_0_60,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_25]),c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_43]),c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_48]),c_0_43])])).

cnf(c_0_63,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(esk5_0,esk6_0)),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_30])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_15]),c_0_16]),c_0_38]),c_0_62])])).

cnf(c_0_66,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_63,c_0_41])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.19/0.53  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.19/0.53  #
% 0.19/0.53  # Preprocessing time       : 0.028 s
% 0.19/0.53  # Presaturation interreduction done
% 0.19/0.53  
% 0.19/0.53  # Proof found!
% 0.19/0.53  # SZS status Theorem
% 0.19/0.53  # SZS output start CNFRefutation
% 0.19/0.53  fof(t22_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_waybel_9)).
% 0.19/0.53  fof(t38_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&X4=X3)&r2_hidden(X2,X4))&v3_pre_topc(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_yellow_6)).
% 0.19/0.53  fof(t39_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))<=>(r2_hidden(X2,X3)&v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 0.19/0.53  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.53  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.53  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.53  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.19/0.53  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.19/0.53  fof(fc6_tops_1, axiom, ![X1, X2, X3]:((((((v2_pre_topc(X1)&l1_pre_topc(X1))&v3_pre_topc(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&v3_pre_topc(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k3_xboole_0(X2,X3),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_tops_1)).
% 0.19/0.53  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.53  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t22_waybel_9])).
% 0.19/0.53  fof(c_0_11, plain, ![X30, X31, X32]:((((m1_subset_1(esk2_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X32,u1_struct_0(k9_yellow_6(X30,X31)))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))&(esk2_3(X30,X31,X32)=X32|~m1_subset_1(X32,u1_struct_0(k9_yellow_6(X30,X31)))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30))))&(r2_hidden(X31,esk2_3(X30,X31,X32))|~m1_subset_1(X32,u1_struct_0(k9_yellow_6(X30,X31)))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30))))&(v3_pre_topc(esk2_3(X30,X31,X32),X30)|~m1_subset_1(X32,u1_struct_0(k9_yellow_6(X30,X31)))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).
% 0.19/0.53  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))&(m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))&~m1_subset_1(k3_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.53  cnf(c_0_13, plain, (esk2_3(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.53  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.53  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.53  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.53  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.53  fof(c_0_18, plain, ![X34, X35, X36]:(((r2_hidden(X35,X36)|~r2_hidden(X36,u1_struct_0(k9_yellow_6(X34,X35)))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(v3_pre_topc(X36,X34)|~r2_hidden(X36,u1_struct_0(k9_yellow_6(X34,X35)))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34))))&(~r2_hidden(X35,X36)|~v3_pre_topc(X36,X34)|r2_hidden(X36,u1_struct_0(k9_yellow_6(X34,X35)))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).
% 0.19/0.53  fof(c_0_19, plain, ![X24, X25, X26]:(~r2_hidden(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(X26))|m1_subset_1(X24,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.53  fof(c_0_20, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.53  fof(c_0_21, plain, ![X20, X21]:k1_setfam_1(k2_tarski(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.53  fof(c_0_22, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X17))|k9_subset_1(X17,X18,X19)=k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.19/0.53  cnf(c_0_23, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.53  cnf(c_0_24, negated_conjecture, (esk2_3(esk3_0,esk4_0,X1)=X1|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.19/0.53  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.53  cnf(c_0_26, plain, (r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))|v2_struct_0(X3)|~r2_hidden(X1,X2)|~v3_pre_topc(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.53  cnf(c_0_27, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.53  fof(c_0_28, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X14))|m1_subset_1(k9_subset_1(X14,X15,X16),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.19/0.53  cnf(c_0_29, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.53  cnf(c_0_30, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.53  cnf(c_0_31, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.53  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.19/0.53  cnf(c_0_33, negated_conjecture, (esk2_3(esk3_0,esk4_0,esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.53  cnf(c_0_34, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.53  cnf(c_0_35, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.53  cnf(c_0_36, plain, (r2_hidden(X1,X4)|X4!=k1_setfam_1(k2_tarski(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.53  cnf(c_0_37, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_31, c_0_30])).
% 0.19/0.53  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25])])).
% 0.19/0.53  cnf(c_0_39, plain, (v2_struct_0(X1)|r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_struct_0(k9_yellow_6(X1,X4)))|~v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X4,k9_subset_1(u1_struct_0(X1),X2,X3))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.53  cnf(c_0_40, plain, (r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_36])).
% 0.19/0.53  cnf(c_0_41, negated_conjecture, (k1_setfam_1(k2_tarski(X1,esk6_0))=k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.53  cnf(c_0_42, plain, (r2_hidden(X1,esk2_3(X2,X1,X3))|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.53  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.53  fof(c_0_44, plain, ![X27, X28, X29]:(~v2_pre_topc(X27)|~l1_pre_topc(X27)|~v3_pre_topc(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~v3_pre_topc(X29,X27)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|v3_pre_topc(k3_xboole_0(X28,X29),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_tops_1])])).
% 0.19/0.53  cnf(c_0_45, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,X2)))|~v3_pre_topc(k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0),esk3_0)|~r2_hidden(X2,k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_38]), c_0_15]), c_0_16])]), c_0_17])).
% 0.19/0.53  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,k9_subset_1(u1_struct_0(esk3_0),X2,esk6_0))|~r2_hidden(X1,esk6_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.53  cnf(c_0_47, negated_conjecture, (r2_hidden(esk4_0,esk2_3(esk3_0,esk4_0,X1))|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.19/0.53  cnf(c_0_48, negated_conjecture, (esk2_3(esk3_0,esk4_0,esk5_0)=esk5_0), inference(spm,[status(thm)],[c_0_24, c_0_43])).
% 0.19/0.53  cnf(c_0_49, plain, (v3_pre_topc(k3_xboole_0(X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.53  cnf(c_0_50, plain, (v3_pre_topc(esk2_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.53  cnf(c_0_51, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,X2)))|~v3_pre_topc(k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0),esk3_0)|~r2_hidden(X2,esk6_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.53  cnf(c_0_52, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_43]), c_0_48])).
% 0.19/0.53  cnf(c_0_53, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_25]), c_0_33])).
% 0.19/0.53  cnf(c_0_54, plain, (v3_pre_topc(k1_setfam_1(k2_tarski(X2,X3)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_49, c_0_30])).
% 0.19/0.53  cnf(c_0_55, negated_conjecture, (v3_pre_topc(esk2_3(esk3_0,esk4_0,X1),esk3_0)|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.19/0.53  cnf(c_0_56, negated_conjecture, (~m1_subset_1(k3_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.53  fof(c_0_57, plain, ![X22, X23]:(~r2_hidden(X22,X23)|m1_subset_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.53  cnf(c_0_58, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))|~v3_pre_topc(k9_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.19/0.53  cnf(c_0_59, negated_conjecture, (v3_pre_topc(k9_subset_1(u1_struct_0(esk3_0),X1,esk6_0),X2)|~v3_pre_topc(esk6_0,X2)|~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_54, c_0_41])).
% 0.19/0.53  cnf(c_0_60, negated_conjecture, (v3_pre_topc(esk6_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_25]), c_0_33])).
% 0.19/0.53  cnf(c_0_61, negated_conjecture, (v3_pre_topc(esk5_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_43]), c_0_48])).
% 0.19/0.53  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_48]), c_0_43])])).
% 0.19/0.53  cnf(c_0_63, negated_conjecture, (~m1_subset_1(k1_setfam_1(k2_tarski(esk5_0,esk6_0)),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_56, c_0_30])).
% 0.19/0.53  cnf(c_0_64, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.53  cnf(c_0_65, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61]), c_0_15]), c_0_16]), c_0_38]), c_0_62])])).
% 0.19/0.53  cnf(c_0_66, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_63, c_0_41])).
% 0.19/0.53  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), ['proof']).
% 0.19/0.53  # SZS output end CNFRefutation
% 0.19/0.53  # Proof object total steps             : 68
% 0.19/0.53  # Proof object clause steps            : 47
% 0.19/0.53  # Proof object formula steps           : 21
% 0.19/0.53  # Proof object conjectures             : 32
% 0.19/0.53  # Proof object clause conjectures      : 29
% 0.19/0.53  # Proof object formula conjectures     : 3
% 0.19/0.53  # Proof object initial clauses used    : 19
% 0.19/0.53  # Proof object initial formulas used   : 10
% 0.19/0.53  # Proof object generating inferences   : 21
% 0.19/0.53  # Proof object simplifying inferences  : 45
% 0.19/0.53  # Training examples: 0 positive, 0 negative
% 0.19/0.53  # Parsed axioms                        : 10
% 0.19/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.53  # Initial clauses                      : 26
% 0.19/0.53  # Removed in clause preprocessing      : 1
% 0.19/0.53  # Initial clauses in saturation        : 25
% 0.19/0.53  # Processed clauses                    : 911
% 0.19/0.53  # ...of these trivial                  : 39
% 0.19/0.53  # ...subsumed                          : 157
% 0.19/0.53  # ...remaining for further processing  : 715
% 0.19/0.53  # Other redundant clauses eliminated   : 3
% 0.19/0.53  # Clauses deleted for lack of memory   : 0
% 0.19/0.53  # Backward-subsumed                    : 2
% 0.19/0.53  # Backward-rewritten                   : 207
% 0.19/0.53  # Generated clauses                    : 5273
% 0.19/0.53  # ...of the previous two non-trivial   : 5230
% 0.19/0.53  # Contextual simplify-reflections      : 2
% 0.19/0.53  # Paramodulations                      : 5234
% 0.19/0.53  # Factorizations                       : 36
% 0.19/0.53  # Equation resolutions                 : 3
% 0.19/0.53  # Propositional unsat checks           : 0
% 0.19/0.53  #    Propositional check models        : 0
% 0.19/0.53  #    Propositional check unsatisfiable : 0
% 0.19/0.53  #    Propositional clauses             : 0
% 0.19/0.53  #    Propositional clauses after purity: 0
% 0.19/0.53  #    Propositional unsat core size     : 0
% 0.19/0.53  #    Propositional preprocessing time  : 0.000
% 0.19/0.53  #    Propositional encoding time       : 0.000
% 0.19/0.53  #    Propositional solver time         : 0.000
% 0.19/0.53  #    Success case prop preproc time    : 0.000
% 0.19/0.53  #    Success case prop encoding time   : 0.000
% 0.19/0.53  #    Success case prop solver time     : 0.000
% 0.19/0.53  # Current number of processed clauses  : 478
% 0.19/0.53  #    Positive orientable unit clauses  : 164
% 0.19/0.53  #    Positive unorientable unit clauses: 0
% 0.19/0.53  #    Negative unit clauses             : 2
% 0.19/0.53  #    Non-unit-clauses                  : 312
% 0.19/0.53  # Current number of unprocessed clauses: 4309
% 0.19/0.53  # ...number of literals in the above   : 16805
% 0.19/0.53  # Current number of archived formulas  : 0
% 0.19/0.53  # Current number of archived clauses   : 235
% 0.19/0.53  # Clause-clause subsumption calls (NU) : 41694
% 0.19/0.53  # Rec. Clause-clause subsumption calls : 28072
% 0.19/0.53  # Non-unit clause-clause subsumptions  : 161
% 0.19/0.53  # Unit Clause-clause subsumption calls : 9609
% 0.19/0.53  # Rewrite failures with RHS unbound    : 0
% 0.19/0.53  # BW rewrite match attempts            : 13791
% 0.19/0.53  # BW rewrite match successes           : 97
% 0.19/0.53  # Condensation attempts                : 0
% 0.19/0.53  # Condensation successes               : 0
% 0.19/0.53  # Termbank termtop insertions          : 149676
% 0.19/0.53  
% 0.19/0.53  # -------------------------------------------------
% 0.19/0.53  # User time                : 0.180 s
% 0.19/0.53  # System time              : 0.011 s
% 0.19/0.53  # Total time               : 0.190 s
% 0.19/0.53  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
