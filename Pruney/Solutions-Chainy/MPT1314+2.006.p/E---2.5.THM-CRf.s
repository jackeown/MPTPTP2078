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
% DateTime   : Thu Dec  3 11:13:17 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 623 expanded)
%              Number of clauses        :   54 ( 275 expanded)
%              Number of leaves         :   11 ( 154 expanded)
%              Depth                    :   16
%              Number of atoms          :  201 (1787 expanded)
%              Number of equality atoms :   47 ( 407 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t33_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v3_pre_topc(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                   => ( X4 = X2
                     => v3_pre_topc(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(t32_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( v3_pre_topc(X3,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X12))
      | m1_subset_1(k9_subset_1(X12,X13,X14),k1_zfmisc_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_pre_topc(X3,X1)
               => ( v3_pre_topc(X2,X1)
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                     => ( X4 = X2
                       => v3_pre_topc(X4,X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_tops_2])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X15))
      | k9_subset_1(X15,X16,X17) = k3_xboole_0(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k3_xboole_0(X7,X8) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_18,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_pre_topc(esk4_0,esk2_0)
    & v3_pre_topc(esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & esk5_0 = esk3_0
    & ~ v3_pre_topc(esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(pm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k9_subset_1(X1,X2,X3)) = k9_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_22,c_0_20]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(pm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k9_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_14,c_0_28])).

cnf(c_0_32,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(pm,[status(thm)],[c_0_22,c_0_29])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k9_subset_1(X1,X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_30,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(esk3_0,u1_struct_0(esk4_0)) = esk3_0 ),
    inference(pm,[status(thm)],[c_0_22,c_0_31])).

fof(c_0_35,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | k9_subset_1(X9,X10,X11) = k9_subset_1(X9,X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_23,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k9_subset_1(X1,u1_struct_0(esk4_0),esk3_0) = k3_xboole_0(X1,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_36,c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(X1,esk3_0)) = k9_subset_1(X1,u1_struct_0(esk4_0),esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_27,c_0_37])).

cnf(c_0_41,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(k3_xboole_0(X1,X2),X4)
    | ~ m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(pm,[status(thm)],[c_0_32,c_0_32])).

fof(c_0_42,plain,(
    ! [X24,X25,X26,X28] :
      ( ( m1_subset_1(esk1_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v3_pre_topc(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X24) )
      & ( v3_pre_topc(esk1_3(X24,X25,X26),X24)
        | ~ v3_pre_topc(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X24) )
      & ( k9_subset_1(u1_struct_0(X25),esk1_3(X24,X25,X26),k2_struct_0(X25)) = X26
        | ~ v3_pre_topc(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v3_pre_topc(X28,X24)
        | k9_subset_1(u1_struct_0(X25),X28,k2_struct_0(X25)) != X26
        | v3_pre_topc(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_pre_topc(X25,X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_tops_2])])])])])).

cnf(c_0_43,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_20,c_0_38])).

cnf(c_0_44,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_39,c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(X1,esk3_0)) = esk3_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_21,c_0_40]),c_0_23]),c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( k3_xboole_0(esk3_0,X1) = k3_xboole_0(esk3_0,X2)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41,c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,plain,
    ( v3_pre_topc(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3)) != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k9_subset_1(X1,u1_struct_0(esk4_0),esk3_0) = k9_subset_1(X1,X1,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_30,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( ~ v3_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k9_subset_1(X1,X2,X3)) = k9_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_22,c_0_43]),c_0_23])).

cnf(c_0_52,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_38,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk3_0,X1)) = esk3_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_45,c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(esk3_0,X1) = k3_xboole_0(esk3_0,X2)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(esk3_0,X2) ),
    inference(pm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) != k9_subset_1(u1_struct_0(X1),X2,X3)
    | ~ v3_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ l1_pre_topc(X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(pm,[status(thm)],[c_0_48,c_0_15])).

cnf(c_0_56,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0),esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_37,c_0_49]),c_0_23]),c_0_34]),c_0_28])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_25])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k9_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(pm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk3_0,X2)) = esk3_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(esk3_0,X2) ),
    inference(pm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0)) != esk3_0
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55,c_0_56]),c_0_56]),c_0_28])]),c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k9_subset_1(X1,esk3_0,X2) = esk3_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(esk3_0,X2) ),
    inference(pm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(esk3_0,k2_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_60,c_0_61]),c_0_28])])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_64,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_66,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_67,plain,(
    ! [X20] :
      ( ~ l1_struct_0(X20)
      | k2_struct_0(X20) = u1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_68,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | l1_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k2_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65]),c_0_66])])).

cnf(c_0_70,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_71,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_72,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69,c_0_70]),c_0_31])])).

cnf(c_0_74,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72,c_0_65]),c_0_66])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_73,c_0_74]),c_0_75])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.54/3.71  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 3.54/3.71  # and selection function NoSelection.
% 3.54/3.71  #
% 3.54/3.71  # Preprocessing time       : 0.028 s
% 3.54/3.71  
% 3.54/3.71  # Proof found!
% 3.54/3.71  # SZS status Theorem
% 3.54/3.71  # SZS output start CNFRefutation
% 3.54/3.71  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.54/3.71  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.54/3.71  fof(t33_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v3_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v3_pre_topc(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 3.54/3.71  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.54/3.71  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.54/3.71  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.54/3.71  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.54/3.71  fof(t32_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(v3_pre_topc(X3,X2)<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_2)).
% 3.54/3.71  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.54/3.71  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.54/3.71  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.54/3.71  fof(c_0_11, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.54/3.71  fof(c_0_12, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X12))|m1_subset_1(k9_subset_1(X12,X13,X14),k1_zfmisc_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 3.54/3.71  fof(c_0_13, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v3_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v3_pre_topc(X4,X3)))))))), inference(assume_negation,[status(cth)],[t33_tops_2])).
% 3.54/3.71  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.54/3.71  cnf(c_0_15, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 3.54/3.71  fof(c_0_16, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(X15))|k9_subset_1(X15,X16,X17)=k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 3.54/3.71  fof(c_0_17, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k3_xboole_0(X7,X8)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 3.54/3.71  fof(c_0_18, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 3.54/3.71  fof(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_pre_topc(esk4_0,esk2_0)&(v3_pre_topc(esk3_0,esk2_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(esk5_0=esk3_0&~v3_pre_topc(esk5_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 3.54/3.71  cnf(c_0_20, plain, (r1_tarski(k9_subset_1(X1,X2,X3),X1)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_14, c_0_15])).
% 3.54/3.71  cnf(c_0_21, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.54/3.71  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.54/3.71  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.54/3.71  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.54/3.71  cnf(c_0_25, negated_conjecture, (esk5_0=esk3_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.54/3.71  cnf(c_0_26, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(pm,[status(thm)],[c_0_20, c_0_21])).
% 3.54/3.71  cnf(c_0_27, plain, (k3_xboole_0(X1,k9_subset_1(X1,X2,X3))=k9_subset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_22, c_0_20]), c_0_23])).
% 3.54/3.71  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 3.54/3.71  cnf(c_0_29, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(pm,[status(thm)],[c_0_26, c_0_23])).
% 3.54/3.71  cnf(c_0_30, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k9_subset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_27, c_0_21])).
% 3.54/3.71  cnf(c_0_31, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk4_0))), inference(pm,[status(thm)],[c_0_14, c_0_28])).
% 3.54/3.71  cnf(c_0_32, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(pm,[status(thm)],[c_0_22, c_0_29])).
% 3.54/3.71  cnf(c_0_33, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k9_subset_1(X1,X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_30, c_0_23])).
% 3.54/3.71  cnf(c_0_34, negated_conjecture, (k3_xboole_0(esk3_0,u1_struct_0(esk4_0))=esk3_0), inference(pm,[status(thm)],[c_0_22, c_0_31])).
% 3.54/3.71  fof(c_0_35, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X9))|k9_subset_1(X9,X10,X11)=k9_subset_1(X9,X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 3.54/3.71  cnf(c_0_36, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_23, c_0_32])).
% 3.54/3.71  cnf(c_0_37, negated_conjecture, (k9_subset_1(X1,u1_struct_0(esk4_0),esk3_0)=k3_xboole_0(X1,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_33, c_0_34])).
% 3.54/3.71  cnf(c_0_38, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 3.54/3.71  cnf(c_0_39, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_36, c_0_23])).
% 3.54/3.71  cnf(c_0_40, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(X1,esk3_0))=k9_subset_1(X1,u1_struct_0(esk4_0),esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_27, c_0_37])).
% 3.54/3.71  cnf(c_0_41, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(k3_xboole_0(X1,X2),X4)|~m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X4))), inference(pm,[status(thm)],[c_0_32, c_0_32])).
% 3.54/3.71  fof(c_0_42, plain, ![X24, X25, X26, X28]:((((m1_subset_1(esk1_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))|~v3_pre_topc(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~m1_pre_topc(X25,X24)|~l1_pre_topc(X24))&(v3_pre_topc(esk1_3(X24,X25,X26),X24)|~v3_pre_topc(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~m1_pre_topc(X25,X24)|~l1_pre_topc(X24)))&(k9_subset_1(u1_struct_0(X25),esk1_3(X24,X25,X26),k2_struct_0(X25))=X26|~v3_pre_topc(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~m1_pre_topc(X25,X24)|~l1_pre_topc(X24)))&(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X24)))|~v3_pre_topc(X28,X24)|k9_subset_1(u1_struct_0(X25),X28,k2_struct_0(X25))!=X26|v3_pre_topc(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~m1_pre_topc(X25,X24)|~l1_pre_topc(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_tops_2])])])])])).
% 3.54/3.71  cnf(c_0_43, plain, (r1_tarski(k9_subset_1(X1,X2,X3),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_20, c_0_38])).
% 3.54/3.71  cnf(c_0_44, plain, (k9_subset_1(X1,X2,X3)=k3_xboole_0(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_39, c_0_30])).
% 3.54/3.71  cnf(c_0_45, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(X1,esk3_0))=esk3_0|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_21, c_0_40]), c_0_23]), c_0_34])).
% 3.54/3.71  cnf(c_0_46, negated_conjecture, (k3_xboole_0(esk3_0,X1)=k3_xboole_0(esk3_0,X2)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41, c_0_34]), c_0_34]), c_0_34])).
% 3.54/3.71  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.54/3.71  cnf(c_0_48, plain, (v3_pre_topc(X4,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3))!=X4|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.54/3.71  cnf(c_0_49, negated_conjecture, (k9_subset_1(X1,u1_struct_0(esk4_0),esk3_0)=k9_subset_1(X1,X1,esk3_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_30, c_0_40])).
% 3.54/3.71  cnf(c_0_50, negated_conjecture, (~v3_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.54/3.71  cnf(c_0_51, plain, (k3_xboole_0(X1,k9_subset_1(X1,X2,X3))=k9_subset_1(X1,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_22, c_0_43]), c_0_23])).
% 3.54/3.71  cnf(c_0_52, plain, (k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_38, c_0_44])).
% 3.54/3.71  cnf(c_0_53, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk3_0,X1))=esk3_0|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_45, c_0_23])).
% 3.54/3.71  cnf(c_0_54, negated_conjecture, (k3_xboole_0(esk3_0,X1)=k3_xboole_0(esk3_0,X2)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_tarski(esk3_0,X2)), inference(pm,[status(thm)],[c_0_46, c_0_47])).
% 3.54/3.71  cnf(c_0_55, plain, (v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)|k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1))!=k9_subset_1(u1_struct_0(X1),X2,X3)|~v3_pre_topc(X4,X5)|~m1_pre_topc(X1,X5)|~l1_pre_topc(X5)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(pm,[status(thm)],[c_0_48, c_0_15])).
% 3.54/3.71  cnf(c_0_56, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0),esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_37, c_0_49]), c_0_23]), c_0_34]), c_0_28])])).
% 3.54/3.71  cnf(c_0_57, negated_conjecture, (~v3_pre_topc(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_50, c_0_25])).
% 3.54/3.71  cnf(c_0_58, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k9_subset_1(X1,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(pm,[status(thm)],[c_0_51, c_0_52])).
% 3.54/3.71  cnf(c_0_59, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk3_0,X2))=esk3_0|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_tarski(esk3_0,X2)), inference(pm,[status(thm)],[c_0_53, c_0_54])).
% 3.54/3.71  cnf(c_0_60, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),X1,k2_struct_0(esk4_0))!=esk3_0|~v3_pre_topc(X1,X2)|~m1_pre_topc(esk4_0,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55, c_0_56]), c_0_56]), c_0_28])]), c_0_57])).
% 3.54/3.71  cnf(c_0_61, negated_conjecture, (k9_subset_1(X1,esk3_0,X2)=esk3_0|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_tarski(esk3_0,X2)), inference(pm,[status(thm)],[c_0_58, c_0_59])).
% 3.54/3.71  cnf(c_0_62, negated_conjecture, (~v3_pre_topc(esk3_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(esk3_0,k2_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_60, c_0_61]), c_0_28])])).
% 3.54/3.71  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.54/3.71  cnf(c_0_64, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.54/3.71  cnf(c_0_65, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.54/3.71  cnf(c_0_66, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.54/3.71  fof(c_0_67, plain, ![X20]:(~l1_struct_0(X20)|k2_struct_0(X20)=u1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 3.54/3.71  fof(c_0_68, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|l1_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 3.54/3.71  cnf(c_0_69, negated_conjecture, (~r1_tarski(esk3_0,k2_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65]), c_0_66])])).
% 3.54/3.71  cnf(c_0_70, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 3.54/3.71  fof(c_0_71, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 3.54/3.71  cnf(c_0_72, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 3.54/3.71  cnf(c_0_73, negated_conjecture, (~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69, c_0_70]), c_0_31])])).
% 3.54/3.71  cnf(c_0_74, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 3.54/3.71  cnf(c_0_75, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72, c_0_65]), c_0_66])])).
% 3.54/3.71  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_73, c_0_74]), c_0_75])]), ['proof']).
% 3.54/3.71  # SZS output end CNFRefutation
% 3.54/3.71  # Proof object total steps             : 77
% 3.54/3.71  # Proof object clause steps            : 54
% 3.54/3.71  # Proof object formula steps           : 23
% 3.54/3.71  # Proof object conjectures             : 30
% 3.54/3.71  # Proof object clause conjectures      : 27
% 3.54/3.71  # Proof object formula conjectures     : 3
% 3.54/3.71  # Proof object initial clauses used    : 18
% 3.54/3.71  # Proof object initial formulas used   : 11
% 3.54/3.71  # Proof object generating inferences   : 34
% 3.54/3.71  # Proof object simplifying inferences  : 28
% 3.54/3.71  # Training examples: 0 positive, 0 negative
% 3.54/3.71  # Parsed axioms                        : 11
% 3.54/3.71  # Removed by relevancy pruning/SinE    : 0
% 3.54/3.71  # Initial clauses                      : 21
% 3.54/3.71  # Removed in clause preprocessing      : 0
% 3.54/3.71  # Initial clauses in saturation        : 21
% 3.54/3.71  # Processed clauses                    : 10638
% 3.54/3.71  # ...of these trivial                  : 176
% 3.54/3.71  # ...subsumed                          : 9216
% 3.54/3.71  # ...remaining for further processing  : 1246
% 3.54/3.71  # Other redundant clauses eliminated   : 0
% 3.54/3.71  # Clauses deleted for lack of memory   : 0
% 3.54/3.71  # Backward-subsumed                    : 89
% 3.54/3.71  # Backward-rewritten                   : 0
% 3.54/3.71  # Generated clauses                    : 484510
% 3.54/3.71  # ...of the previous two non-trivial   : 482658
% 3.54/3.71  # Contextual simplify-reflections      : 0
% 3.54/3.71  # Paramodulations                      : 484476
% 3.54/3.71  # Factorizations                       : 0
% 3.54/3.71  # Equation resolutions                 : 34
% 3.54/3.71  # Propositional unsat checks           : 0
% 3.54/3.71  #    Propositional check models        : 0
% 3.54/3.71  #    Propositional check unsatisfiable : 0
% 3.54/3.71  #    Propositional clauses             : 0
% 3.54/3.71  #    Propositional clauses after purity: 0
% 3.54/3.71  #    Propositional unsat core size     : 0
% 3.54/3.71  #    Propositional preprocessing time  : 0.000
% 3.54/3.71  #    Propositional encoding time       : 0.000
% 3.54/3.71  #    Propositional solver time         : 0.000
% 3.54/3.71  #    Success case prop preproc time    : 0.000
% 3.54/3.71  #    Success case prop encoding time   : 0.000
% 3.54/3.71  #    Success case prop solver time     : 0.000
% 3.54/3.71  # Current number of processed clauses  : 1157
% 3.54/3.71  #    Positive orientable unit clauses  : 19
% 3.54/3.71  #    Positive unorientable unit clauses: 1
% 3.54/3.71  #    Negative unit clauses             : 3
% 3.54/3.71  #    Non-unit-clauses                  : 1134
% 3.54/3.71  # Current number of unprocessed clauses: 471428
% 3.54/3.71  # ...number of literals in the above   : 2369898
% 3.54/3.71  # Current number of archived formulas  : 0
% 3.54/3.71  # Current number of archived clauses   : 89
% 3.54/3.71  # Clause-clause subsumption calls (NU) : 280425
% 3.54/3.71  # Rec. Clause-clause subsumption calls : 191067
% 3.54/3.71  # Non-unit clause-clause subsumptions  : 9294
% 3.54/3.71  # Unit Clause-clause subsumption calls : 2062
% 3.54/3.71  # Rewrite failures with RHS unbound    : 0
% 3.54/3.71  # BW rewrite match attempts            : 4
% 3.54/3.71  # BW rewrite match successes           : 0
% 3.54/3.71  # Condensation attempts                : 0
% 3.54/3.71  # Condensation successes               : 0
% 3.54/3.71  # Termbank termtop insertions          : 6897065
% 3.54/3.72  
% 3.54/3.72  # -------------------------------------------------
% 3.54/3.72  # User time                : 3.213 s
% 3.54/3.72  # System time              : 0.172 s
% 3.54/3.72  # Total time               : 3.386 s
% 3.54/3.72  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
