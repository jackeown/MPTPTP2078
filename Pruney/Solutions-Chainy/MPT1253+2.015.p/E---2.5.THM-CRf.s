%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:07 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 128 expanded)
%              Number of clauses        :   30 (  48 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  136 ( 365 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(t42_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(d2_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_tops_1])).

fof(c_0_14,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X35))
      | k9_subset_1(X35,X36,X37) = k9_subset_1(X35,X37,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

fof(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & v4_pre_topc(esk3_0,esk2_0)
    & ~ r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X55,X56] :
      ( ( ~ v4_pre_topc(X56,X55)
        | k2_pre_topc(X55,X56) = X56
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ l1_pre_topc(X55) )
      & ( ~ v2_pre_topc(X55)
        | k2_pre_topc(X55,X56) != X56
        | v4_pre_topc(X56,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ l1_pre_topc(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_17,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | ~ m1_subset_1(X48,k1_zfmisc_1(X46))
      | r1_tarski(k3_subset_1(X46,X47),k3_subset_1(X46,k9_subset_1(X46,X47,X48))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t42_subset_1])])])).

fof(c_0_18,plain,(
    ! [X53,X54] :
      ( ~ l1_pre_topc(X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
      | m1_subset_1(k2_pre_topc(X53,X54),k1_zfmisc_1(u1_struct_0(X53))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_19,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | m1_subset_1(k9_subset_1(X40,X41,X42),k1_zfmisc_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_20,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X57,X58] :
      ( ~ l1_pre_topc(X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
      | k2_tops_1(X57,X58) = k9_subset_1(u1_struct_0(X57),k2_pre_topc(X57,X58),k2_pre_topc(X57,k3_subset_1(u1_struct_0(X57),X58))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_1])])])).

cnf(c_0_23,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_26,plain,(
    ! [X24,X25] : r1_tarski(k4_xboole_0(X24,X25),X24) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_27,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_28,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | k3_subset_1(X38,X39) = k4_xboole_0(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_29,plain,(
    ! [X43,X44,X45] :
      ( ( ~ r1_tarski(X44,X45)
        | r1_tarski(k3_subset_1(X43,X45),k3_subset_1(X43,X44))
        | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(X43)) )
      & ( ~ r1_tarski(k3_subset_1(X43,X45),k3_subset_1(X43,X44))
        | r1_tarski(X44,X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
        | ~ m1_subset_1(X44,k1_zfmisc_1(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

cnf(c_0_30,plain,
    ( r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,k9_subset_1(X2,X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),esk3_0,X1) = k9_subset_1(u1_struct_0(esk2_0),X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_34,plain,
    ( k2_tops_1(X1,X2) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_21]),c_0_24]),c_0_25])])).

cnf(c_0_36,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_38,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_39,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(X1),X2),k3_subset_1(u1_struct_0(X1),k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_21])])).

cnf(c_0_43,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),esk3_0,k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))) = k2_tops_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_21]),c_0_25])]),c_0_35])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_50,plain,(
    ! [X49,X50] :
      ( ( ~ m1_subset_1(X49,k1_zfmisc_1(X50))
        | r1_tarski(X49,X50) )
      & ( ~ r1_tarski(X49,X50)
        | m1_subset_1(X49,k1_zfmisc_1(X50)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_51,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk2_0),k3_xboole_0(esk3_0,u1_struct_0(esk2_0))) = k3_subset_1(u1_struct_0(esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_21]),c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_43]),c_0_25]),c_0_48]),c_0_21])]),c_0_49])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.78/0.99  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.78/0.99  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.78/0.99  #
% 0.78/0.99  # Preprocessing time       : 0.028 s
% 0.78/0.99  # Presaturation interreduction done
% 0.78/0.99  
% 0.78/0.99  # Proof found!
% 0.78/0.99  # SZS status Theorem
% 0.78/0.99  # SZS output start CNFRefutation
% 0.78/0.99  fof(t69_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 0.78/0.99  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.78/0.99  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.78/0.99  fof(t42_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 0.78/0.99  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.78/0.99  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.78/0.99  fof(d2_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 0.78/0.99  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.78/0.99  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.78/0.99  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.78/0.99  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 0.78/0.99  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.78/0.99  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.78/0.99  fof(c_0_13, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t69_tops_1])).
% 0.78/0.99  fof(c_0_14, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(X35))|k9_subset_1(X35,X36,X37)=k9_subset_1(X35,X37,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.78/0.99  fof(c_0_15, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(v4_pre_topc(esk3_0,esk2_0)&~r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.78/0.99  fof(c_0_16, plain, ![X55, X56]:((~v4_pre_topc(X56,X55)|k2_pre_topc(X55,X56)=X56|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|~l1_pre_topc(X55))&(~v2_pre_topc(X55)|k2_pre_topc(X55,X56)!=X56|v4_pre_topc(X56,X55)|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|~l1_pre_topc(X55))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.78/0.99  fof(c_0_17, plain, ![X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|(~m1_subset_1(X48,k1_zfmisc_1(X46))|r1_tarski(k3_subset_1(X46,X47),k3_subset_1(X46,k9_subset_1(X46,X47,X48))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t42_subset_1])])])).
% 0.78/0.99  fof(c_0_18, plain, ![X53, X54]:(~l1_pre_topc(X53)|~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))|m1_subset_1(k2_pre_topc(X53,X54),k1_zfmisc_1(u1_struct_0(X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.78/0.99  fof(c_0_19, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(X40))|m1_subset_1(k9_subset_1(X40,X41,X42),k1_zfmisc_1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.78/0.99  cnf(c_0_20, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.78/0.99  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.78/0.99  fof(c_0_22, plain, ![X57, X58]:(~l1_pre_topc(X57)|(~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|k2_tops_1(X57,X58)=k9_subset_1(u1_struct_0(X57),k2_pre_topc(X57,X58),k2_pre_topc(X57,k3_subset_1(u1_struct_0(X57),X58))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_1])])])).
% 0.78/0.99  cnf(c_0_23, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.78/0.99  cnf(c_0_24, negated_conjecture, (v4_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.78/0.99  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.78/0.99  fof(c_0_26, plain, ![X24, X25]:r1_tarski(k4_xboole_0(X24,X25),X24), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.78/0.99  fof(c_0_27, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.78/0.99  fof(c_0_28, plain, ![X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(X38))|k3_subset_1(X38,X39)=k4_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.78/0.99  fof(c_0_29, plain, ![X43, X44, X45]:((~r1_tarski(X44,X45)|r1_tarski(k3_subset_1(X43,X45),k3_subset_1(X43,X44))|~m1_subset_1(X45,k1_zfmisc_1(X43))|~m1_subset_1(X44,k1_zfmisc_1(X43)))&(~r1_tarski(k3_subset_1(X43,X45),k3_subset_1(X43,X44))|r1_tarski(X44,X45)|~m1_subset_1(X45,k1_zfmisc_1(X43))|~m1_subset_1(X44,k1_zfmisc_1(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 0.78/0.99  cnf(c_0_30, plain, (r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,k9_subset_1(X2,X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.99  cnf(c_0_31, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.99  cnf(c_0_32, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.78/0.99  cnf(c_0_33, negated_conjecture, (k9_subset_1(u1_struct_0(esk2_0),esk3_0,X1)=k9_subset_1(u1_struct_0(esk2_0),X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.78/0.99  cnf(c_0_34, plain, (k2_tops_1(X1,X2)=k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.78/0.99  cnf(c_0_35, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_21]), c_0_24]), c_0_25])])).
% 0.78/0.99  cnf(c_0_36, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.78/0.99  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.78/0.99  fof(c_0_38, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.78/0.99  cnf(c_0_39, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.78/0.99  cnf(c_0_40, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.78/0.99  cnf(c_0_41, plain, (r1_tarski(k3_subset_1(u1_struct_0(X1),X2),k3_subset_1(u1_struct_0(X1),k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.78/0.99  cnf(c_0_42, negated_conjecture, (m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_21])])).
% 0.78/0.99  cnf(c_0_43, negated_conjecture, (k9_subset_1(u1_struct_0(esk2_0),esk3_0,k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)))=k2_tops_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_21]), c_0_25])]), c_0_35])).
% 0.78/0.99  cnf(c_0_44, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.78/0.99  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.78/0.99  cnf(c_0_46, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_39, c_0_37])).
% 0.78/0.99  cnf(c_0_47, plain, (r1_tarski(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),X2)|~l1_pre_topc(X1)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.78/0.99  cnf(c_0_48, negated_conjecture, (m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.78/0.99  cnf(c_0_49, negated_conjecture, (~r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.78/0.99  fof(c_0_50, plain, ![X49, X50]:((~m1_subset_1(X49,k1_zfmisc_1(X50))|r1_tarski(X49,X50))&(~r1_tarski(X49,X50)|m1_subset_1(X49,k1_zfmisc_1(X50)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.78/0.99  cnf(c_0_51, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.78/0.99  cnf(c_0_52, negated_conjecture, (k5_xboole_0(u1_struct_0(esk2_0),k3_xboole_0(esk3_0,u1_struct_0(esk2_0)))=k3_subset_1(u1_struct_0(esk2_0),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_21]), c_0_45])).
% 0.78/0.99  cnf(c_0_53, negated_conjecture, (~m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_43]), c_0_25]), c_0_48]), c_0_21])]), c_0_49])).
% 0.78/0.99  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.78/0.99  cnf(c_0_55, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.78/0.99  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])]), ['proof']).
% 0.78/0.99  # SZS output end CNFRefutation
% 0.78/0.99  # Proof object total steps             : 57
% 0.78/0.99  # Proof object clause steps            : 30
% 0.78/0.99  # Proof object formula steps           : 27
% 0.78/0.99  # Proof object conjectures             : 16
% 0.78/0.99  # Proof object clause conjectures      : 13
% 0.78/0.99  # Proof object formula conjectures     : 3
% 0.78/0.99  # Proof object initial clauses used    : 16
% 0.78/0.99  # Proof object initial formulas used   : 13
% 0.78/0.99  # Proof object generating inferences   : 12
% 0.78/0.99  # Proof object simplifying inferences  : 18
% 0.78/0.99  # Training examples: 0 positive, 0 negative
% 0.78/0.99  # Parsed axioms                        : 24
% 0.78/0.99  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.99  # Initial clauses                      : 34
% 0.78/0.99  # Removed in clause preprocessing      : 1
% 0.78/0.99  # Initial clauses in saturation        : 33
% 0.78/0.99  # Processed clauses                    : 7364
% 0.78/0.99  # ...of these trivial                  : 193
% 0.78/0.99  # ...subsumed                          : 5782
% 0.78/0.99  # ...remaining for further processing  : 1389
% 0.78/0.99  # Other redundant clauses eliminated   : 2
% 0.78/0.99  # Clauses deleted for lack of memory   : 0
% 0.78/0.99  # Backward-subsumed                    : 20
% 0.78/0.99  # Backward-rewritten                   : 45
% 0.78/0.99  # Generated clauses                    : 74537
% 0.78/0.99  # ...of the previous two non-trivial   : 64008
% 0.78/0.99  # Contextual simplify-reflections      : 4
% 0.78/0.99  # Paramodulations                      : 74532
% 0.78/0.99  # Factorizations                       : 0
% 0.78/0.99  # Equation resolutions                 : 2
% 0.78/0.99  # Propositional unsat checks           : 0
% 0.78/0.99  #    Propositional check models        : 0
% 0.78/0.99  #    Propositional check unsatisfiable : 0
% 0.78/0.99  #    Propositional clauses             : 0
% 0.78/0.99  #    Propositional clauses after purity: 0
% 0.78/0.99  #    Propositional unsat core size     : 0
% 0.78/0.99  #    Propositional preprocessing time  : 0.000
% 0.78/0.99  #    Propositional encoding time       : 0.000
% 0.78/0.99  #    Propositional solver time         : 0.000
% 0.78/0.99  #    Success case prop preproc time    : 0.000
% 0.78/0.99  #    Success case prop encoding time   : 0.000
% 0.78/0.99  #    Success case prop solver time     : 0.000
% 0.78/0.99  # Current number of processed clauses  : 1289
% 0.78/0.99  #    Positive orientable unit clauses  : 255
% 0.78/0.99  #    Positive unorientable unit clauses: 33
% 0.78/0.99  #    Negative unit clauses             : 101
% 0.78/0.99  #    Non-unit-clauses                  : 900
% 0.78/0.99  # Current number of unprocessed clauses: 56366
% 0.78/0.99  # ...number of literals in the above   : 130770
% 0.78/0.99  # Current number of archived formulas  : 0
% 0.78/0.99  # Current number of archived clauses   : 98
% 0.78/0.99  # Clause-clause subsumption calls (NU) : 212638
% 0.78/0.99  # Rec. Clause-clause subsumption calls : 173604
% 0.78/0.99  # Non-unit clause-clause subsumptions  : 3716
% 0.78/0.99  # Unit Clause-clause subsumption calls : 15768
% 0.78/0.99  # Rewrite failures with RHS unbound    : 0
% 0.78/0.99  # BW rewrite match attempts            : 2155
% 0.78/0.99  # BW rewrite match successes           : 42
% 0.78/0.99  # Condensation attempts                : 0
% 0.78/0.99  # Condensation successes               : 0
% 0.78/0.99  # Termbank termtop insertions          : 1183262
% 0.78/1.00  
% 0.78/1.00  # -------------------------------------------------
% 0.78/1.00  # User time                : 0.615 s
% 0.78/1.00  # System time              : 0.037 s
% 0.78/1.00  # Total time               : 0.652 s
% 0.78/1.00  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
