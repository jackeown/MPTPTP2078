%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:36 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 271 expanded)
%              Number of clauses        :   69 ( 120 expanded)
%              Number of leaves         :   19 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  251 ( 679 expanded)
%              Number of equality atoms :   37 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t32_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)),k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t50_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => k2_pre_topc(X1,k4_subset_1(u1_struct_0(X1),X2,X3)) = k4_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t49_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(c_0_19,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_20,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_21,plain,(
    ! [X16,X17] : k2_xboole_0(X16,k4_xboole_0(X17,X16)) = k2_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(k4_xboole_0(X21,X22),X23)
      | r1_tarski(X21,k2_xboole_0(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_25,plain,(
    ! [X24,X25] : r1_tarski(X24,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_28,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,k2_xboole_0(X19,X20))
      | r1_tarski(k4_xboole_0(X18,X19),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)),k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_tops_1])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k4_xboole_0(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X38,X39] :
      ( ( ~ m1_subset_1(X38,k1_zfmisc_1(X39))
        | r1_tarski(X38,X39) )
      & ( ~ r1_tarski(X38,X39)
        | m1_subset_1(X38,k1_zfmisc_1(X39)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0)),k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,k2_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_38,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | k3_subset_1(X26,X27) = k4_xboole_0(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_42,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | k3_subset_1(X30,k3_subset_1(X30,X31)) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_43,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | m1_subset_1(k3_subset_1(X28,X29),k1_zfmisc_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_37,c_0_31])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_48,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | k7_subset_1(X35,X36,X37) = k4_xboole_0(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_49,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | r1_tarski(k4_xboole_0(X8,X10),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_50,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_55,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0)),k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_57,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_58,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | ~ m1_subset_1(X34,k1_zfmisc_1(X32))
      | k4_subset_1(X32,X33,X34) = k2_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_59,plain,(
    ! [X45,X46,X47] :
      ( ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
      | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
      | k2_pre_topc(X45,k4_subset_1(u1_struct_0(X45),X46,X47)) = k4_subset_1(u1_struct_0(X45),k2_pre_topc(X45,X46),k2_pre_topc(X45,X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_pre_topc])])])).

fof(c_0_60,plain,(
    ! [X40,X41] :
      ( ~ l1_pre_topc(X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
      | m1_subset_1(k2_pre_topc(X40,X41),k1_zfmisc_1(u1_struct_0(X40))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_61,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k3_subset_1(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(k4_xboole_0(X1,u1_struct_0(esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0)),k2_pre_topc(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_40])])).

fof(c_0_67,plain,(
    ! [X42,X43,X44] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
      | ~ r1_tarski(X43,X44)
      | r1_tarski(k2_pre_topc(X42,X43),k2_pre_topc(X42,X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

cnf(c_0_68,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( k2_pre_topc(X1,k4_subset_1(u1_struct_0(X1),X2,X3)) = k4_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_22])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k2_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_33]),c_0_23])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0)),k2_pre_topc(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_57])).

cnf(c_0_77,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( k2_pre_topc(X1,k4_subset_1(u1_struct_0(X1),X2,X3)) = k2_xboole_0(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_70])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_33])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_40])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_73])).

cnf(c_0_82,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_85,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_xboole_0(k2_pre_topc(esk1_0,esk3_0),k2_pre_topc(esk1_0,k4_xboole_0(esk2_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_33])).

cnf(c_0_86,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_xboole_0(k2_pre_topc(X1,X3),k2_pre_topc(X1,X4)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(X1),X3,X4),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k4_subset_1(u1_struct_0(X1),X3,X4)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_88,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_89,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_79,c_0_61])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(u1_struct_0(esk1_0),X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_31])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(X2,u1_struct_0(esk1_0)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_81])).

cnf(c_0_92,negated_conjecture,
    ( k2_xboole_0(esk2_0,u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])])).

cnf(c_0_93,negated_conjecture,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(esk1_0),esk3_0,k4_xboole_0(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,k4_subset_1(u1_struct_0(esk1_0),esk3_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_88]),c_0_40]),c_0_63])])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(k4_xboole_0(X1,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_70])).

cnf(c_0_97,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_68]),c_0_26]),c_0_23]),c_0_26]),c_0_23]),c_0_31]),c_0_63])])).

cnf(c_0_98,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_73])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_33])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_pre_topc(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_75])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_40]),c_0_88])])).

cnf(c_0_105,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_98]),c_0_103])])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_75])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_98]),c_0_106])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:23:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.38/0.58  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.38/0.58  #
% 0.38/0.58  # Preprocessing time       : 0.028 s
% 0.38/0.58  # Presaturation interreduction done
% 0.38/0.58  
% 0.38/0.58  # Proof found!
% 0.38/0.58  # SZS status Theorem
% 0.38/0.58  # SZS output start CNFRefutation
% 0.38/0.58  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.38/0.58  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.38/0.58  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.38/0.58  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.38/0.58  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.38/0.58  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.38/0.58  fof(t32_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)),k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_1)).
% 0.38/0.58  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.38/0.58  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.38/0.58  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.38/0.58  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.38/0.58  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.38/0.58  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.38/0.58  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 0.38/0.58  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.38/0.58  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.38/0.58  fof(t50_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,k4_subset_1(u1_struct_0(X1),X2,X3))=k4_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_pre_topc)).
% 0.38/0.58  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.38/0.58  fof(t49_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 0.38/0.58  fof(c_0_19, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.38/0.58  fof(c_0_20, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.38/0.58  fof(c_0_21, plain, ![X16, X17]:k2_xboole_0(X16,k4_xboole_0(X17,X16))=k2_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.38/0.58  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.38/0.58  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.58  fof(c_0_24, plain, ![X21, X22, X23]:(~r1_tarski(k4_xboole_0(X21,X22),X23)|r1_tarski(X21,k2_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.38/0.58  fof(c_0_25, plain, ![X24, X25]:r1_tarski(X24,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.38/0.58  cnf(c_0_26, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.58  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.38/0.58  fof(c_0_28, plain, ![X18, X19, X20]:(~r1_tarski(X18,k2_xboole_0(X19,X20))|r1_tarski(k4_xboole_0(X18,X19),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.38/0.58  fof(c_0_29, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)),k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),X2,X3))))))), inference(assume_negation,[status(cth)],[t32_tops_1])).
% 0.38/0.58  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.38/0.58  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.38/0.58  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k4_xboole_0(X2,X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.38/0.58  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.58  fof(c_0_34, plain, ![X38, X39]:((~m1_subset_1(X38,k1_zfmisc_1(X39))|r1_tarski(X38,X39))&(~r1_tarski(X38,X39)|m1_subset_1(X38,k1_zfmisc_1(X39)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.38/0.58  fof(c_0_35, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0)),k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.38/0.58  cnf(c_0_36, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),X3)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.38/0.58  cnf(c_0_37, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,k2_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.38/0.58  fof(c_0_38, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.38/0.58  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.38/0.58  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.38/0.58  fof(c_0_41, plain, ![X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|k3_subset_1(X26,X27)=k4_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.38/0.58  fof(c_0_42, plain, ![X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|k3_subset_1(X30,k3_subset_1(X30,X31))=X31), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.38/0.58  fof(c_0_43, plain, ![X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(X28))|m1_subset_1(k3_subset_1(X28,X29),k1_zfmisc_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.38/0.58  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r1_tarski(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_36, c_0_27])).
% 0.38/0.58  cnf(c_0_45, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_37, c_0_31])).
% 0.38/0.58  cnf(c_0_46, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.38/0.58  cnf(c_0_47, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.38/0.58  fof(c_0_48, plain, ![X35, X36, X37]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|k7_subset_1(X35,X36,X37)=k4_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.38/0.58  fof(c_0_49, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|r1_tarski(k4_xboole_0(X8,X10),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 0.38/0.58  cnf(c_0_50, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.38/0.58  cnf(c_0_51, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.38/0.58  cnf(c_0_52, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.38/0.58  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~r1_tarski(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.38/0.58  cnf(c_0_54, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.38/0.58  fof(c_0_55, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.38/0.58  cnf(c_0_56, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0)),k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.38/0.58  cnf(c_0_57, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.38/0.58  fof(c_0_58, plain, ![X32, X33, X34]:(~m1_subset_1(X33,k1_zfmisc_1(X32))|~m1_subset_1(X34,k1_zfmisc_1(X32))|k4_subset_1(X32,X33,X34)=k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.38/0.58  fof(c_0_59, plain, ![X45, X46, X47]:(~v2_pre_topc(X45)|~l1_pre_topc(X45)|(~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|(~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|k2_pre_topc(X45,k4_subset_1(u1_struct_0(X45),X46,X47))=k4_subset_1(u1_struct_0(X45),k2_pre_topc(X45,X46),k2_pre_topc(X45,X47))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_pre_topc])])])).
% 0.38/0.58  fof(c_0_60, plain, ![X40, X41]:(~l1_pre_topc(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|m1_subset_1(k2_pre_topc(X40,X41),k1_zfmisc_1(u1_struct_0(X40)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.38/0.58  cnf(c_0_61, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.38/0.58  cnf(c_0_62, plain, (k4_xboole_0(X1,k3_subset_1(X1,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.38/0.58  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.38/0.58  cnf(c_0_64, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(k4_xboole_0(X1,u1_struct_0(esk1_0)),esk2_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.38/0.58  cnf(c_0_65, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.38/0.58  cnf(c_0_66, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0)),k2_pre_topc(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_40])])).
% 0.38/0.58  fof(c_0_67, plain, ![X42, X43, X44]:(~l1_pre_topc(X42)|(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|(~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|(~r1_tarski(X43,X44)|r1_tarski(k2_pre_topc(X42,X43),k2_pre_topc(X42,X44)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).
% 0.38/0.58  cnf(c_0_68, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.38/0.58  cnf(c_0_69, plain, (k2_pre_topc(X1,k4_subset_1(u1_struct_0(X1),X2,X3))=k4_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.38/0.58  cnf(c_0_70, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.38/0.58  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_44, c_0_22])).
% 0.38/0.58  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.38/0.58  cnf(c_0_73, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_39, c_0_63])).
% 0.38/0.58  cnf(c_0_74, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k2_xboole_0(esk2_0,u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_33]), c_0_23])).
% 0.38/0.58  cnf(c_0_75, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_65])).
% 0.38/0.58  cnf(c_0_76, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0)),k2_pre_topc(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_66, c_0_57])).
% 0.38/0.58  cnf(c_0_77, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.38/0.58  cnf(c_0_78, plain, (k2_pre_topc(X1,k4_subset_1(u1_struct_0(X1),X2,X3))=k2_xboole_0(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_70])).
% 0.38/0.58  cnf(c_0_79, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_71, c_0_33])).
% 0.38/0.58  cnf(c_0_80, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_72, c_0_40])).
% 0.38/0.58  cnf(c_0_81, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_73])).
% 0.38/0.58  cnf(c_0_82, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.38/0.58  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.38/0.58  cnf(c_0_84, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_31, c_0_23])).
% 0.38/0.58  cnf(c_0_85, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_xboole_0(k2_pre_topc(esk1_0,esk3_0),k2_pre_topc(esk1_0,k4_xboole_0(esk2_0,esk3_0))))), inference(spm,[status(thm)],[c_0_76, c_0_33])).
% 0.38/0.58  cnf(c_0_86, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_xboole_0(k2_pre_topc(X1,X3),k2_pre_topc(X1,X4)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k4_subset_1(u1_struct_0(X1),X3,X4),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k4_subset_1(u1_struct_0(X1),X3,X4))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.38/0.58  cnf(c_0_87, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.38/0.58  cnf(c_0_88, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.38/0.58  cnf(c_0_89, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X3,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_79, c_0_61])).
% 0.38/0.58  cnf(c_0_90, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(u1_struct_0(esk1_0),X1))), inference(spm,[status(thm)],[c_0_80, c_0_31])).
% 0.38/0.58  cnf(c_0_91, negated_conjecture, (r1_tarski(X1,k2_xboole_0(X2,u1_struct_0(esk1_0)))|~r1_tarski(k4_xboole_0(X1,X2),esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_81])).
% 0.38/0.58  cnf(c_0_92, negated_conjecture, (k2_xboole_0(esk2_0,u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])])).
% 0.38/0.58  cnf(c_0_93, negated_conjecture, (~m1_subset_1(k4_subset_1(u1_struct_0(esk1_0),esk3_0,k4_xboole_0(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,k4_subset_1(u1_struct_0(esk1_0),esk3_0,k4_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87]), c_0_88]), c_0_40]), c_0_63])])).
% 0.38/0.58  cnf(c_0_94, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))|~r1_tarski(X2,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.38/0.58  cnf(c_0_95, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(k4_xboole_0(X1,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.38/0.58  cnf(c_0_96, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_39, c_0_70])).
% 0.38/0.58  cnf(c_0_97, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_68]), c_0_26]), c_0_23]), c_0_26]), c_0_23]), c_0_31]), c_0_63])])).
% 0.38/0.58  cnf(c_0_98, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.38/0.58  cnf(c_0_99, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_94, c_0_73])).
% 0.38/0.58  cnf(c_0_100, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k2_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_95, c_0_33])).
% 0.38/0.58  cnf(c_0_101, plain, (r1_tarski(X1,u1_struct_0(X2))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_pre_topc(X2,X3))), inference(spm,[status(thm)],[c_0_46, c_0_96])).
% 0.38/0.58  cnf(c_0_102, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])])).
% 0.38/0.58  cnf(c_0_103, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_100, c_0_75])).
% 0.38/0.58  cnf(c_0_104, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_40]), c_0_88])])).
% 0.38/0.58  cnf(c_0_105, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_98]), c_0_103])])).
% 0.38/0.58  cnf(c_0_106, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_104, c_0_75])).
% 0.38/0.58  cnf(c_0_107, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_98]), c_0_106])]), ['proof']).
% 0.38/0.58  # SZS output end CNFRefutation
% 0.38/0.58  # Proof object total steps             : 108
% 0.38/0.58  # Proof object clause steps            : 69
% 0.38/0.58  # Proof object formula steps           : 39
% 0.38/0.58  # Proof object conjectures             : 34
% 0.38/0.58  # Proof object clause conjectures      : 31
% 0.38/0.58  # Proof object formula conjectures     : 3
% 0.38/0.58  # Proof object initial clauses used    : 25
% 0.38/0.58  # Proof object initial formulas used   : 19
% 0.38/0.58  # Proof object generating inferences   : 43
% 0.38/0.58  # Proof object simplifying inferences  : 29
% 0.38/0.58  # Training examples: 0 positive, 0 negative
% 0.38/0.58  # Parsed axioms                        : 19
% 0.38/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.58  # Initial clauses                      : 26
% 0.38/0.58  # Removed in clause preprocessing      : 0
% 0.38/0.58  # Initial clauses in saturation        : 26
% 0.38/0.58  # Processed clauses                    : 3476
% 0.38/0.58  # ...of these trivial                  : 60
% 0.38/0.58  # ...subsumed                          : 2718
% 0.38/0.58  # ...remaining for further processing  : 698
% 0.38/0.58  # Other redundant clauses eliminated   : 2
% 0.38/0.58  # Clauses deleted for lack of memory   : 0
% 0.38/0.58  # Backward-subsumed                    : 50
% 0.38/0.58  # Backward-rewritten                   : 49
% 0.38/0.58  # Generated clauses                    : 18104
% 0.38/0.58  # ...of the previous two non-trivial   : 15880
% 0.38/0.58  # Contextual simplify-reflections      : 8
% 0.38/0.58  # Paramodulations                      : 18102
% 0.38/0.58  # Factorizations                       : 0
% 0.38/0.58  # Equation resolutions                 : 2
% 0.38/0.58  # Propositional unsat checks           : 0
% 0.38/0.58  #    Propositional check models        : 0
% 0.38/0.58  #    Propositional check unsatisfiable : 0
% 0.38/0.58  #    Propositional clauses             : 0
% 0.38/0.58  #    Propositional clauses after purity: 0
% 0.38/0.58  #    Propositional unsat core size     : 0
% 0.38/0.58  #    Propositional preprocessing time  : 0.000
% 0.38/0.58  #    Propositional encoding time       : 0.000
% 0.38/0.58  #    Propositional solver time         : 0.000
% 0.38/0.58  #    Success case prop preproc time    : 0.000
% 0.38/0.58  #    Success case prop encoding time   : 0.000
% 0.38/0.58  #    Success case prop solver time     : 0.000
% 0.38/0.58  # Current number of processed clauses  : 572
% 0.38/0.58  #    Positive orientable unit clauses  : 66
% 0.38/0.58  #    Positive unorientable unit clauses: 3
% 0.38/0.58  #    Negative unit clauses             : 10
% 0.38/0.58  #    Non-unit-clauses                  : 493
% 0.38/0.58  # Current number of unprocessed clauses: 12179
% 0.38/0.58  # ...number of literals in the above   : 35928
% 0.38/0.58  # Current number of archived formulas  : 0
% 0.38/0.58  # Current number of archived clauses   : 124
% 0.38/0.58  # Clause-clause subsumption calls (NU) : 111444
% 0.38/0.58  # Rec. Clause-clause subsumption calls : 80560
% 0.38/0.58  # Non-unit clause-clause subsumptions  : 2251
% 0.38/0.58  # Unit Clause-clause subsumption calls : 1989
% 0.38/0.58  # Rewrite failures with RHS unbound    : 32
% 0.38/0.58  # BW rewrite match attempts            : 313
% 0.38/0.58  # BW rewrite match successes           : 44
% 0.38/0.58  # Condensation attempts                : 0
% 0.38/0.58  # Condensation successes               : 0
% 0.38/0.58  # Termbank termtop insertions          : 216523
% 0.38/0.58  
% 0.38/0.58  # -------------------------------------------------
% 0.38/0.58  # User time                : 0.243 s
% 0.38/0.58  # System time              : 0.007 s
% 0.38/0.58  # Total time               : 0.250 s
% 0.38/0.58  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
