%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:58 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 452 expanded)
%              Number of clauses        :   67 ( 205 expanded)
%              Number of leaves         :   12 ( 107 expanded)
%              Depth                    :   23
%              Number of atoms          :  220 (1273 expanded)
%              Number of equality atoms :    8 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t64_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_xboole_0(X2,X4) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

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

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_tops_1])).

fof(c_0_13,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | m1_subset_1(k1_tops_1(X32,X33),k1_zfmisc_1(u1_struct_0(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X29))
      | k7_subset_1(X29,X30,X31) = k4_xboole_0(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_xboole_0(X14,X15)
      | r1_xboole_0(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_21,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | r1_xboole_0(X20,k4_xboole_0(X22,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_22,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | r1_tarski(k1_tops_1(X34,X35),X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_23,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | m1_subset_1(k7_subset_1(X26,X27,X28),k1_zfmisc_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

cnf(c_0_24,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,X1),X2) = k4_xboole_0(k1_tops_1(esk1_0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_26,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_xboole_0(X23,X25)
      | r1_tarski(X23,k4_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X18,X19)
      | ~ r1_xboole_0(X17,X19)
      | r1_xboole_0(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk3_0),X1) = k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_35,plain,(
    ! [X5,X6] : r1_tarski(k4_xboole_0(X5,X6),X5) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r1_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4)))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X5)
    | ~ r1_tarski(X5,X4) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_25])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,k4_xboole_0(X3,X4))
    | ~ r1_tarski(X1,X5)
    | ~ r1_tarski(X5,X4) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1)),k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X4)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X5)
    | ~ r1_tarski(X5,X4) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_41]),c_0_25])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X3,k4_xboole_0(X4,X5))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X6)
    | ~ r1_tarski(X6,X5) ),
    inference(spm,[status(thm)],[c_0_33,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1)),k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_19]),c_0_25])])).

cnf(c_0_48,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X4)))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_44,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk3_0,X1)),k4_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X3))))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_52,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X4)))
    | ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X5,X6)),X4)
    | ~ r1_tarski(X1,X6) ),
    inference(spm,[status(thm)],[c_0_44,c_0_48])).

fof(c_0_53,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(k4_xboole_0(X10,X11),X12)
      | r1_tarski(X10,k2_xboole_0(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,X3))))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1))))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X1)))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_52,c_0_40])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,X1))))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1))))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_51])).

cnf(c_0_60,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X1)))
    | ~ r1_tarski(k4_xboole_0(X1,X4),X5) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,X1))))
    | ~ r1_tarski(k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X2))),X1)
    | ~ r1_tarski(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,esk3_0))))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_40])).

cnf(c_0_64,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X4)))
    | ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X5,X1)),X4) ),
    inference(spm,[status(thm)],[c_0_44,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,esk3_0))))
    | ~ r1_tarski(k4_xboole_0(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_57])).

cnf(c_0_66,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X4,X1))))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_68,plain,(
    ! [X36,X37,X38] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ r1_tarski(X37,X38)
      | r1_tarski(k1_tops_1(X36,X37),k1_tops_1(X36,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k4_xboole_0(X1,X2)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_51])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_67])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k4_xboole_0(X1,X2)))
    | ~ r1_tarski(k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,esk3_0))),X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_71]),c_0_67])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k4_xboole_0(X1,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_40])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k4_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(X3,k4_xboole_0(X4,esk3_0))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k4_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(X2,X3)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k1_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_74]),c_0_40])])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(X1,k4_xboole_0(k4_xboole_0(X3,esk3_0),X4))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_40])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k4_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(X2,X3)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),X3) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_82,c_0_71])).

cnf(c_0_86,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),X1) = k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_67])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(X1,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),X1)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_67])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(X1,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_81])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:34:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.24/2.48  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S050I
% 2.24/2.48  # and selection function PSelectNewComplexExceptUniqMaxHorn.
% 2.24/2.48  #
% 2.24/2.48  # Preprocessing time       : 0.027 s
% 2.24/2.48  # Presaturation interreduction done
% 2.24/2.48  
% 2.24/2.48  # Proof found!
% 2.24/2.48  # SZS status Theorem
% 2.24/2.48  # SZS output start CNFRefutation
% 2.24/2.48  fof(t50_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 2.24/2.48  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.24/2.48  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.24/2.48  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.24/2.48  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.24/2.48  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.24/2.48  fof(dt_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 2.24/2.48  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.24/2.48  fof(t64_xboole_1, axiom, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&r1_tarski(X3,X4))&r1_xboole_0(X2,X4))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 2.24/2.48  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.24/2.48  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.24/2.48  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 2.24/2.48  fof(c_0_12, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t50_tops_1])).
% 2.24/2.48  fof(c_0_13, plain, ![X32, X33]:(~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|m1_subset_1(k1_tops_1(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 2.24/2.48  fof(c_0_14, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 2.24/2.48  fof(c_0_15, plain, ![X29, X30, X31]:(~m1_subset_1(X30,k1_zfmisc_1(X29))|k7_subset_1(X29,X30,X31)=k4_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 2.24/2.48  cnf(c_0_16, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.24/2.48  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.24/2.48  cnf(c_0_18, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.24/2.48  cnf(c_0_19, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 2.24/2.48  fof(c_0_20, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_xboole_0(X14,X15)|r1_xboole_0(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 2.24/2.48  fof(c_0_21, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|r1_xboole_0(X20,k4_xboole_0(X22,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 2.24/2.48  fof(c_0_22, plain, ![X34, X35]:(~l1_pre_topc(X34)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|r1_tarski(k1_tops_1(X34,X35),X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 2.24/2.48  fof(c_0_23, plain, ![X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|m1_subset_1(k7_subset_1(X26,X27,X28),k1_zfmisc_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).
% 2.24/2.48  cnf(c_0_24, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,X1),X2)=k4_xboole_0(k1_tops_1(esk1_0,X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 2.24/2.48  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.24/2.48  fof(c_0_26, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_xboole_0(X23,X25)|r1_tarski(X23,k4_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 2.24/2.48  cnf(c_0_27, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.24/2.48  cnf(c_0_28, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.24/2.48  fof(c_0_29, plain, ![X16, X17, X18, X19]:(~r1_tarski(X16,X17)|~r1_tarski(X18,X19)|~r1_xboole_0(X17,X19)|r1_xboole_0(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).
% 2.24/2.48  cnf(c_0_30, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.24/2.48  cnf(c_0_31, plain, (m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.24/2.48  cnf(c_0_32, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk3_0),X1)=k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 2.24/2.48  cnf(c_0_33, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.24/2.48  cnf(c_0_34, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 2.24/2.48  fof(c_0_35, plain, ![X5, X6]:r1_tarski(k4_xboole_0(X5,X6),X5), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 2.24/2.48  cnf(c_0_36, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)|~r1_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.24/2.48  cnf(c_0_37, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_30, c_0_17])).
% 2.24/2.48  cnf(c_0_38, negated_conjecture, (m1_subset_1(k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 2.24/2.48  cnf(c_0_39, plain, (r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4)))|~r1_tarski(X1,X2)|~r1_tarski(X1,X5)|~r1_tarski(X5,X4)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 2.24/2.48  cnf(c_0_40, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.24/2.48  cnf(c_0_41, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1)=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_25])).
% 2.24/2.48  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X2,k4_xboole_0(X3,X4))|~r1_tarski(X1,X5)|~r1_tarski(X5,X4)), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 2.24/2.48  cnf(c_0_43, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1)),k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1))|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.24/2.48  cnf(c_0_44, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X4)))|~r1_tarski(k4_xboole_0(X1,X2),X5)|~r1_tarski(X5,X4)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 2.24/2.48  cnf(c_0_45, negated_conjecture, (m1_subset_1(k4_xboole_0(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_41]), c_0_25])])).
% 2.24/2.48  cnf(c_0_46, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X3,k4_xboole_0(X4,X5))|~r1_tarski(X1,X2)|~r1_tarski(X1,X6)|~r1_tarski(X6,X5)), inference(spm,[status(thm)],[c_0_33, c_0_42])).
% 2.24/2.48  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1)),k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_19]), c_0_25])])).
% 2.24/2.48  cnf(c_0_48, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X4)))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_44, c_0_40])).
% 2.24/2.48  cnf(c_0_49, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk3_0,X1)),k4_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_37, c_0_45])).
% 2.24/2.48  cnf(c_0_50, negated_conjecture, (r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X3))))|~r1_tarski(X1,X2)|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 2.24/2.48  cnf(c_0_51, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_25])).
% 2.24/2.48  cnf(c_0_52, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X4)))|~r1_tarski(k4_xboole_0(X1,k4_xboole_0(X5,X6)),X4)|~r1_tarski(X1,X6)), inference(spm,[status(thm)],[c_0_44, c_0_48])).
% 2.24/2.48  fof(c_0_53, plain, ![X10, X11, X12]:(~r1_tarski(k4_xboole_0(X10,X11),X12)|r1_tarski(X10,k2_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 2.24/2.48  cnf(c_0_54, negated_conjecture, (r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,X3))))|~r1_tarski(X1,X2)|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_46, c_0_49])).
% 2.24/2.48  cnf(c_0_55, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1))))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 2.24/2.48  cnf(c_0_56, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X1)))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_52, c_0_40])).
% 2.24/2.48  cnf(c_0_57, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 2.24/2.48  cnf(c_0_58, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,X1))))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_54, c_0_51])).
% 2.24/2.48  cnf(c_0_59, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X1))))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_51])).
% 2.24/2.48  cnf(c_0_60, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X1)))|~r1_tarski(k4_xboole_0(X1,X4),X5)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 2.24/2.48  cnf(c_0_61, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,X1))))|~r1_tarski(k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk3_0),X2))),X1)|~r1_tarski(esk3_0,X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 2.24/2.48  cnf(c_0_62, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_60, c_0_40])).
% 2.24/2.48  cnf(c_0_63, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,esk3_0))))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_40])).
% 2.24/2.48  cnf(c_0_64, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,X4)))|~r1_tarski(k4_xboole_0(X1,k4_xboole_0(X5,X1)),X4)), inference(spm,[status(thm)],[c_0_44, c_0_62])).
% 2.24/2.48  cnf(c_0_65, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,esk3_0))))|~r1_tarski(k4_xboole_0(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_63, c_0_57])).
% 2.24/2.48  cnf(c_0_66, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X4,X1)))))), inference(spm,[status(thm)],[c_0_64, c_0_62])).
% 2.24/2.48  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.24/2.48  fof(c_0_68, plain, ![X36, X37, X38]:(~l1_pre_topc(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|(~r1_tarski(X37,X38)|r1_tarski(k1_tops_1(X36,X37),k1_tops_1(X36,X38)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 2.24/2.48  cnf(c_0_69, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k4_xboole_0(X1,X2)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_39, c_0_51])).
% 2.24/2.48  cnf(c_0_70, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,esk3_0))))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 2.24/2.48  cnf(c_0_71, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_67])).
% 2.24/2.48  cnf(c_0_72, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 2.24/2.48  cnf(c_0_73, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k4_xboole_0(X1,X2)))|~r1_tarski(k4_xboole_0(esk3_0,k1_tops_1(esk1_0,k4_xboole_0(esk3_0,esk3_0))),X2)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 2.24/2.48  cnf(c_0_74, negated_conjecture, (m1_subset_1(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_71]), c_0_67])])).
% 2.24/2.48  cnf(c_0_75, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_72, c_0_17])).
% 2.24/2.48  cnf(c_0_76, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(esk3_0,k4_xboole_0(X1,esk3_0)))), inference(spm,[status(thm)],[c_0_73, c_0_40])).
% 2.24/2.48  cnf(c_0_77, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k4_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_37, c_0_74])).
% 2.24/2.48  cnf(c_0_78, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_75, c_0_67])).
% 2.24/2.48  cnf(c_0_79, negated_conjecture, (r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,esk3_0)))|~r1_tarski(X3,k4_xboole_0(X4,esk3_0))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_46, c_0_76])).
% 2.24/2.48  cnf(c_0_80, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k4_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(X2,X3)))|~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_39, c_0_77])).
% 2.24/2.48  cnf(c_0_81, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k1_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_74]), c_0_40])])).
% 2.24/2.48  cnf(c_0_82, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.24/2.48  cnf(c_0_83, negated_conjecture, (r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,esk3_0)))|~r1_tarski(X1,k4_xboole_0(k4_xboole_0(X3,esk3_0),X4))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_79, c_0_40])).
% 2.24/2.48  cnf(c_0_84, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k4_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(X2,X3)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),X3)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 2.24/2.48  cnf(c_0_85, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_82, c_0_71])).
% 2.24/2.48  cnf(c_0_86, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),X1)=k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_67])).
% 2.24/2.48  cnf(c_0_87, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(X1,k1_tops_1(esk1_0,esk3_0)))|~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),X1)|~r1_tarski(k1_tops_1(esk1_0,esk2_0),X2)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 2.24/2.48  cnf(c_0_88, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_67])).
% 2.24/2.48  cnf(c_0_89, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 2.24/2.48  cnf(c_0_90, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(X1,k1_tops_1(esk1_0,esk3_0)))|~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 2.24/2.48  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_81])]), ['proof']).
% 2.24/2.48  # SZS output end CNFRefutation
% 2.24/2.48  # Proof object total steps             : 92
% 2.24/2.48  # Proof object clause steps            : 67
% 2.24/2.48  # Proof object formula steps           : 25
% 2.24/2.48  # Proof object conjectures             : 47
% 2.24/2.48  # Proof object clause conjectures      : 44
% 2.24/2.48  # Proof object formula conjectures     : 3
% 2.24/2.48  # Proof object initial clauses used    : 15
% 2.24/2.48  # Proof object initial formulas used   : 12
% 2.24/2.48  # Proof object generating inferences   : 50
% 2.24/2.48  # Proof object simplifying inferences  : 12
% 2.24/2.48  # Training examples: 0 positive, 0 negative
% 2.24/2.48  # Parsed axioms                        : 13
% 2.24/2.48  # Removed by relevancy pruning/SinE    : 0
% 2.24/2.48  # Initial clauses                      : 17
% 2.24/2.48  # Removed in clause preprocessing      : 0
% 2.24/2.48  # Initial clauses in saturation        : 17
% 2.24/2.48  # Processed clauses                    : 5991
% 2.24/2.48  # ...of these trivial                  : 86
% 2.24/2.48  # ...subsumed                          : 2392
% 2.24/2.48  # ...remaining for further processing  : 3513
% 2.24/2.48  # Other redundant clauses eliminated   : 0
% 2.24/2.48  # Clauses deleted for lack of memory   : 0
% 2.24/2.48  # Backward-subsumed                    : 433
% 2.24/2.48  # Backward-rewritten                   : 30
% 2.24/2.48  # Generated clauses                    : 147816
% 2.24/2.48  # ...of the previous two non-trivial   : 147608
% 2.24/2.48  # Contextual simplify-reflections      : 0
% 2.24/2.48  # Paramodulations                      : 147816
% 2.24/2.48  # Factorizations                       : 0
% 2.24/2.48  # Equation resolutions                 : 0
% 2.24/2.48  # Propositional unsat checks           : 0
% 2.24/2.48  #    Propositional check models        : 0
% 2.24/2.48  #    Propositional check unsatisfiable : 0
% 2.24/2.48  #    Propositional clauses             : 0
% 2.24/2.48  #    Propositional clauses after purity: 0
% 2.24/2.48  #    Propositional unsat core size     : 0
% 2.24/2.48  #    Propositional preprocessing time  : 0.000
% 2.24/2.48  #    Propositional encoding time       : 0.000
% 2.24/2.48  #    Propositional solver time         : 0.000
% 2.24/2.48  #    Success case prop preproc time    : 0.000
% 2.24/2.48  #    Success case prop encoding time   : 0.000
% 2.24/2.48  #    Success case prop solver time     : 0.000
% 2.24/2.48  # Current number of processed clauses  : 3033
% 2.24/2.48  #    Positive orientable unit clauses  : 227
% 2.24/2.48  #    Positive unorientable unit clauses: 0
% 2.24/2.48  #    Negative unit clauses             : 5
% 2.24/2.48  #    Non-unit-clauses                  : 2801
% 2.24/2.48  # Current number of unprocessed clauses: 141091
% 2.24/2.48  # ...number of literals in the above   : 750703
% 2.24/2.48  # Current number of archived formulas  : 0
% 2.24/2.48  # Current number of archived clauses   : 480
% 2.24/2.48  # Clause-clause subsumption calls (NU) : 969421
% 2.24/2.48  # Rec. Clause-clause subsumption calls : 615306
% 2.24/2.48  # Non-unit clause-clause subsumptions  : 2811
% 2.24/2.48  # Unit Clause-clause subsumption calls : 7342
% 2.24/2.48  # Rewrite failures with RHS unbound    : 0
% 2.24/2.48  # BW rewrite match attempts            : 4459
% 2.24/2.48  # BW rewrite match successes           : 34
% 2.24/2.48  # Condensation attempts                : 0
% 2.24/2.48  # Condensation successes               : 0
% 2.24/2.48  # Termbank termtop insertions          : 4747714
% 2.24/2.48  
% 2.24/2.48  # -------------------------------------------------
% 2.24/2.48  # User time                : 2.074 s
% 2.24/2.48  # System time              : 0.061 s
% 2.24/2.48  # Total time               : 2.135 s
% 2.24/2.48  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
