%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:12 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 344 expanded)
%              Number of clauses        :   42 ( 136 expanded)
%              Number of leaves         :   15 (  86 expanded)
%              Depth                    :    9
%              Number of atoms          :  164 ( 945 expanded)
%              Number of equality atoms :   52 ( 209 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t75_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k2_tops_1(X1,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(l79_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,k2_tops_1(X1,X2)) = k2_tops_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l79_tops_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(l80_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => k2_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k2_tops_1(X1,k2_tops_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t75_tops_1])).

fof(c_0_16,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k3_subset_1(X31,X32) = k4_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & k2_tops_1(esk2_0,k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0))) != k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X52,X53] :
      ( ~ l1_pre_topc(X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
      | k2_tops_1(X52,X53) = k2_tops_1(X52,k3_subset_1(u1_struct_0(X52),X53)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

cnf(c_0_19,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X38,X39] :
      ( ( ~ m1_subset_1(X38,k1_zfmisc_1(X39))
        | r1_tarski(X38,X39) )
      & ( ~ r1_tarski(X38,X39)
        | m1_subset_1(X38,k1_zfmisc_1(X39)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_22,plain,(
    ! [X42,X43] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
      | m1_subset_1(k2_pre_topc(X42,X43),k1_zfmisc_1(u1_struct_0(X42))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_23,plain,(
    ! [X44,X45] :
      ( ~ l1_pre_topc(X44)
      | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
      | m1_subset_1(k2_tops_1(X44,X45),k1_zfmisc_1(u1_struct_0(X44))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_24,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),esk3_0) = k4_xboole_0(u1_struct_0(esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_27,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | k7_subset_1(X35,X36,X37) = k4_xboole_0(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_28,plain,(
    ! [X46,X47] :
      ( ~ l1_pre_topc(X46)
      | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
      | k2_tops_1(X46,X47) = k7_subset_1(u1_struct_0(X46),k2_pre_topc(X46,X47),k1_tops_1(X46,X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X48,X49] :
      ( ~ v2_pre_topc(X48)
      | ~ l1_pre_topc(X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
      | k2_pre_topc(X48,k2_tops_1(X48,X49)) = k2_tops_1(X48,X49) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l79_tops_1])])])).

fof(c_0_32,plain,(
    ! [X15] : k3_xboole_0(X15,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_33,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( k2_tops_1(esk2_0,k4_xboole_0(u1_struct_0(esk2_0),esk3_0)) = k2_tops_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_20]),c_0_25])]),c_0_26])).

fof(c_0_36,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_37,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,plain,
    ( k2_pre_topc(X1,k2_tops_1(X1,X2)) = k2_tops_1(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_42,plain,(
    ! [X50,X51] :
      ( ~ v2_pre_topc(X50)
      | ~ l1_pre_topc(X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
      | k1_tops_1(X50,k2_tops_1(X50,k2_tops_1(X50,X51))) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l80_tops_1])])])).

fof(c_0_43,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_25])])).

cnf(c_0_47,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)) = k2_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_25])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_20]),c_0_25])])).

cnf(c_0_51,plain,
    ( k2_pre_topc(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k2_tops_1(X1,k2_tops_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,plain,
    ( k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k1_xboole_0
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_54,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k2_tops_1(X1,X2)),k1_tops_1(X1,k2_tops_1(X1,X2))) = k2_tops_1(X1,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

cnf(c_0_58,plain,
    ( r1_tarski(k2_pre_topc(X1,k2_tops_1(X1,X2)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_38]),c_0_47])])).

cnf(c_0_60,negated_conjecture,
    ( k2_tops_1(esk2_0,esk3_0) = k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_61,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0))) = k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_20]),c_0_52]),c_0_25])])).

cnf(c_0_62,negated_conjecture,
    ( k1_tops_1(esk2_0,k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_20]),c_0_52]),c_0_25])])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( k2_tops_1(esk2_0,k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0))) != k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k2_pre_topc(X1,k2_tops_1(X1,X2)),k1_tops_1(X1,k2_tops_1(X1,X2))) = k2_tops_1(X1,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_57]),c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_tops_1(esk2_0,k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)))) = k2_tops_1(esk2_0,k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_60]),c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( k1_tops_1(esk2_0,k2_tops_1(esk2_0,k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_60])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_47])])).

cnf(c_0_71,negated_conjecture,
    ( k2_tops_1(esk2_0,k2_tops_1(esk2_0,k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)))) != k2_tops_1(esk2_0,k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_60]),c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69]),c_0_70]),c_0_25])]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.54/0.70  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.54/0.70  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.54/0.70  #
% 0.54/0.70  # Preprocessing time       : 0.029 s
% 0.54/0.70  # Presaturation interreduction done
% 0.54/0.70  
% 0.54/0.70  # Proof found!
% 0.54/0.70  # SZS status Theorem
% 0.54/0.70  # SZS output start CNFRefutation
% 0.54/0.70  fof(t75_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k2_tops_1(X1,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_tops_1)).
% 0.54/0.70  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.54/0.70  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 0.54/0.70  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.54/0.70  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.54/0.70  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.54/0.70  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.54/0.70  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 0.54/0.70  fof(l79_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,k2_tops_1(X1,X2))=k2_tops_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l79_tops_1)).
% 0.54/0.70  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.54/0.70  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.54/0.70  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.54/0.70  fof(l80_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l80_tops_1)).
% 0.54/0.70  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.54/0.70  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.54/0.70  fof(c_0_15, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k2_tops_1(X1,k2_tops_1(X1,X2))))), inference(assume_negation,[status(cth)],[t75_tops_1])).
% 0.54/0.70  fof(c_0_16, plain, ![X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|k3_subset_1(X31,X32)=k4_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.54/0.70  fof(c_0_17, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&k2_tops_1(esk2_0,k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0)))!=k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.54/0.70  fof(c_0_18, plain, ![X52, X53]:(~l1_pre_topc(X52)|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))|k2_tops_1(X52,X53)=k2_tops_1(X52,k3_subset_1(u1_struct_0(X52),X53)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 0.54/0.70  cnf(c_0_19, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.54/0.70  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.70  fof(c_0_21, plain, ![X38, X39]:((~m1_subset_1(X38,k1_zfmisc_1(X39))|r1_tarski(X38,X39))&(~r1_tarski(X38,X39)|m1_subset_1(X38,k1_zfmisc_1(X39)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.54/0.70  fof(c_0_22, plain, ![X42, X43]:(~l1_pre_topc(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|m1_subset_1(k2_pre_topc(X42,X43),k1_zfmisc_1(u1_struct_0(X42)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.54/0.70  fof(c_0_23, plain, ![X44, X45]:(~l1_pre_topc(X44)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|m1_subset_1(k2_tops_1(X44,X45),k1_zfmisc_1(u1_struct_0(X44)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.54/0.70  cnf(c_0_24, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.54/0.70  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.70  cnf(c_0_26, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),esk3_0)=k4_xboole_0(u1_struct_0(esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.54/0.70  fof(c_0_27, plain, ![X35, X36, X37]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|k7_subset_1(X35,X36,X37)=k4_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.54/0.70  fof(c_0_28, plain, ![X46, X47]:(~l1_pre_topc(X46)|(~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))|k2_tops_1(X46,X47)=k7_subset_1(u1_struct_0(X46),k2_pre_topc(X46,X47),k1_tops_1(X46,X47)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.54/0.70  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.54/0.70  cnf(c_0_30, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.54/0.70  fof(c_0_31, plain, ![X48, X49]:(~v2_pre_topc(X48)|~l1_pre_topc(X48)|(~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|k2_pre_topc(X48,k2_tops_1(X48,X49))=k2_tops_1(X48,X49))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l79_tops_1])])])).
% 0.54/0.70  fof(c_0_32, plain, ![X15]:k3_xboole_0(X15,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.54/0.70  fof(c_0_33, plain, ![X22, X23]:k4_xboole_0(X22,k4_xboole_0(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.54/0.70  cnf(c_0_34, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.54/0.70  cnf(c_0_35, negated_conjecture, (k2_tops_1(esk2_0,k4_xboole_0(u1_struct_0(esk2_0),esk3_0))=k2_tops_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_20]), c_0_25])]), c_0_26])).
% 0.54/0.70  fof(c_0_36, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.54/0.70  cnf(c_0_37, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.54/0.70  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.54/0.70  cnf(c_0_39, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.54/0.70  cnf(c_0_40, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.54/0.70  cnf(c_0_41, plain, (k2_pre_topc(X1,k2_tops_1(X1,X2))=k2_tops_1(X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.54/0.70  fof(c_0_42, plain, ![X50, X51]:(~v2_pre_topc(X50)|~l1_pre_topc(X50)|(~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))|k1_tops_1(X50,k2_tops_1(X50,k2_tops_1(X50,X51)))=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l80_tops_1])])])).
% 0.54/0.70  fof(c_0_43, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.54/0.70  cnf(c_0_44, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.54/0.70  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.54/0.70  cnf(c_0_46, negated_conjecture, (m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k4_xboole_0(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_25])])).
% 0.54/0.70  cnf(c_0_47, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.54/0.70  cnf(c_0_48, plain, (k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.54/0.70  cnf(c_0_49, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0))=k2_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_20]), c_0_25])])).
% 0.54/0.70  cnf(c_0_50, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_20]), c_0_25])])).
% 0.54/0.70  cnf(c_0_51, plain, (k2_pre_topc(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k2_tops_1(X1,k2_tops_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_41, c_0_34])).
% 0.54/0.70  cnf(c_0_52, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.70  cnf(c_0_53, plain, (k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k1_xboole_0|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.54/0.70  fof(c_0_54, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.54/0.70  cnf(c_0_55, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.54/0.70  cnf(c_0_56, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.54/0.70  cnf(c_0_57, plain, (k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k2_tops_1(X1,X2)),k1_tops_1(X1,k2_tops_1(X1,X2)))=k2_tops_1(X1,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 0.54/0.70  cnf(c_0_58, plain, (r1_tarski(k2_pre_topc(X1,k2_tops_1(X1,X2)),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.54/0.70  cnf(c_0_59, negated_conjecture, (m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_38]), c_0_47])])).
% 0.54/0.70  cnf(c_0_60, negated_conjecture, (k2_tops_1(esk2_0,esk3_0)=k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.54/0.70  cnf(c_0_61, negated_conjecture, (k2_pre_topc(esk2_0,k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0)))=k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_20]), c_0_52]), c_0_25])])).
% 0.54/0.70  cnf(c_0_62, negated_conjecture, (k1_tops_1(esk2_0,k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_20]), c_0_52]), c_0_25])])).
% 0.54/0.70  cnf(c_0_63, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.54/0.70  cnf(c_0_64, plain, (r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.54/0.70  cnf(c_0_65, negated_conjecture, (k2_tops_1(esk2_0,k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0)))!=k2_tops_1(esk2_0,k2_tops_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.70  cnf(c_0_66, plain, (k4_xboole_0(k2_pre_topc(X1,k2_tops_1(X1,X2)),k1_tops_1(X1,k2_tops_1(X1,X2)))=k2_tops_1(X1,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_57]), c_0_58])).
% 0.54/0.70  cnf(c_0_67, negated_conjecture, (m1_subset_1(k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.54/0.70  cnf(c_0_68, negated_conjecture, (k2_pre_topc(esk2_0,k2_tops_1(esk2_0,k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0))))=k2_tops_1(esk2_0,k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_60]), c_0_60])).
% 0.54/0.70  cnf(c_0_69, negated_conjecture, (k1_tops_1(esk2_0,k2_tops_1(esk2_0,k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_62, c_0_60])).
% 0.54/0.70  cnf(c_0_70, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_47])])).
% 0.54/0.70  cnf(c_0_71, negated_conjecture, (k2_tops_1(esk2_0,k2_tops_1(esk2_0,k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0))))!=k2_tops_1(esk2_0,k4_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_60]), c_0_60])).
% 0.54/0.70  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69]), c_0_70]), c_0_25])]), c_0_71]), ['proof']).
% 0.54/0.70  # SZS output end CNFRefutation
% 0.54/0.70  # Proof object total steps             : 73
% 0.54/0.70  # Proof object clause steps            : 42
% 0.54/0.70  # Proof object formula steps           : 31
% 0.54/0.70  # Proof object conjectures             : 21
% 0.54/0.70  # Proof object clause conjectures      : 18
% 0.54/0.70  # Proof object formula conjectures     : 3
% 0.54/0.70  # Proof object initial clauses used    : 19
% 0.54/0.70  # Proof object initial formulas used   : 15
% 0.54/0.70  # Proof object generating inferences   : 18
% 0.54/0.70  # Proof object simplifying inferences  : 35
% 0.54/0.70  # Training examples: 0 positive, 0 negative
% 0.54/0.70  # Parsed axioms                        : 24
% 0.54/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.54/0.70  # Initial clauses                      : 34
% 0.54/0.70  # Removed in clause preprocessing      : 1
% 0.54/0.70  # Initial clauses in saturation        : 33
% 0.54/0.70  # Processed clauses                    : 4833
% 0.54/0.70  # ...of these trivial                  : 118
% 0.54/0.70  # ...subsumed                          : 3843
% 0.54/0.70  # ...remaining for further processing  : 872
% 0.54/0.70  # Other redundant clauses eliminated   : 2
% 0.54/0.70  # Clauses deleted for lack of memory   : 0
% 0.54/0.70  # Backward-subsumed                    : 21
% 0.54/0.70  # Backward-rewritten                   : 52
% 0.54/0.70  # Generated clauses                    : 37111
% 0.54/0.70  # ...of the previous two non-trivial   : 30950
% 0.54/0.70  # Contextual simplify-reflections      : 12
% 0.54/0.70  # Paramodulations                      : 37029
% 0.54/0.70  # Factorizations                       : 4
% 0.54/0.70  # Equation resolutions                 : 63
% 0.54/0.70  # Propositional unsat checks           : 0
% 0.54/0.70  #    Propositional check models        : 0
% 0.54/0.70  #    Propositional check unsatisfiable : 0
% 0.54/0.70  #    Propositional clauses             : 0
% 0.54/0.70  #    Propositional clauses after purity: 0
% 0.54/0.70  #    Propositional unsat core size     : 0
% 0.54/0.70  #    Propositional preprocessing time  : 0.000
% 0.54/0.70  #    Propositional encoding time       : 0.000
% 0.54/0.70  #    Propositional solver time         : 0.000
% 0.54/0.70  #    Success case prop preproc time    : 0.000
% 0.54/0.70  #    Success case prop encoding time   : 0.000
% 0.54/0.70  #    Success case prop solver time     : 0.000
% 0.54/0.70  # Current number of processed clauses  : 758
% 0.54/0.70  #    Positive orientable unit clauses  : 115
% 0.54/0.70  #    Positive unorientable unit clauses: 5
% 0.54/0.70  #    Negative unit clauses             : 68
% 0.54/0.70  #    Non-unit-clauses                  : 570
% 0.54/0.70  # Current number of unprocessed clauses: 25962
% 0.54/0.70  # ...number of literals in the above   : 67889
% 0.54/0.70  # Current number of archived formulas  : 0
% 0.54/0.70  # Current number of archived clauses   : 109
% 0.54/0.70  # Clause-clause subsumption calls (NU) : 58166
% 0.54/0.70  # Rec. Clause-clause subsumption calls : 44135
% 0.54/0.70  # Non-unit clause-clause subsumptions  : 1863
% 0.54/0.70  # Unit Clause-clause subsumption calls : 4631
% 0.54/0.70  # Rewrite failures with RHS unbound    : 0
% 0.54/0.70  # BW rewrite match attempts            : 219
% 0.54/0.70  # BW rewrite match successes           : 25
% 0.54/0.70  # Condensation attempts                : 0
% 0.54/0.70  # Condensation successes               : 0
% 0.54/0.70  # Termbank termtop insertions          : 402706
% 0.54/0.71  
% 0.54/0.71  # -------------------------------------------------
% 0.54/0.71  # User time                : 0.343 s
% 0.54/0.71  # System time              : 0.017 s
% 0.54/0.71  # Total time               : 0.360 s
% 0.54/0.71  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
