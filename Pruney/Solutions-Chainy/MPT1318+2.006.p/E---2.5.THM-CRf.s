%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:23 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 121 expanded)
%              Number of clauses        :   29 (  49 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  164 ( 280 expanded)
%              Number of equality atoms :   89 ( 135 expanded)
%              Maximal formula depth    :   42 (   5 average)
%              Maximal clause size      :   60 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t81_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(d5_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( X8 = k5_enumset1(X1,X2,X3,X4,X5,X6,X7)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X9 != X1
              & X9 != X2
              & X9 != X3
              & X9 != X4
              & X9 != X5
              & X9 != X6
              & X9 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3)))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_tops_2])).

fof(c_0_15,plain,(
    ! [X62,X63] : k1_setfam_1(k2_tarski(X62,X63)) = k3_xboole_0(X62,X63) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ~ m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk2_0,esk4_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_18,plain,(
    ! [X68,X69] :
      ( ~ l1_pre_topc(X68)
      | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
      | u1_struct_0(k1_pre_topc(X68,X69)) = X69 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_19,plain,(
    ! [X59,X60,X61] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(X59))
      | k9_subset_1(X59,X60,X61) = k3_xboole_0(X60,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X19,X20,X21,X22,X23] : k4_enumset1(X19,X19,X20,X21,X22,X23) = k3_enumset1(X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X31,X32,X33,X34,X35,X36] : k6_enumset1(X31,X31,X31,X32,X33,X34,X35,X36) = k4_enumset1(X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t81_enumset1])).

cnf(c_0_26,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk2_0,esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_30,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X37))
      | k9_subset_1(X37,X38,X39) = k9_subset_1(X37,X39,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_31,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_38,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

fof(c_0_40,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57] :
      ( ( ~ r2_hidden(X48,X47)
        | X48 = X40
        | X48 = X41
        | X48 = X42
        | X48 = X43
        | X48 = X44
        | X48 = X45
        | X48 = X46
        | X47 != k5_enumset1(X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X40
        | r2_hidden(X49,X47)
        | X47 != k5_enumset1(X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X41
        | r2_hidden(X49,X47)
        | X47 != k5_enumset1(X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X42
        | r2_hidden(X49,X47)
        | X47 != k5_enumset1(X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X43
        | r2_hidden(X49,X47)
        | X47 != k5_enumset1(X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X44
        | r2_hidden(X49,X47)
        | X47 != k5_enumset1(X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X45
        | r2_hidden(X49,X47)
        | X47 != k5_enumset1(X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X46
        | r2_hidden(X49,X47)
        | X47 != k5_enumset1(X40,X41,X42,X43,X44,X45,X46) )
      & ( esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) != X50
        | ~ r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k5_enumset1(X50,X51,X52,X53,X54,X55,X56) )
      & ( esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) != X51
        | ~ r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k5_enumset1(X50,X51,X52,X53,X54,X55,X56) )
      & ( esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) != X52
        | ~ r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k5_enumset1(X50,X51,X52,X53,X54,X55,X56) )
      & ( esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) != X53
        | ~ r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k5_enumset1(X50,X51,X52,X53,X54,X55,X56) )
      & ( esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) != X54
        | ~ r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k5_enumset1(X50,X51,X52,X53,X54,X55,X56) )
      & ( esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) != X55
        | ~ r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k5_enumset1(X50,X51,X52,X53,X54,X55,X56) )
      & ( esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) != X56
        | ~ r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | X57 = k5_enumset1(X50,X51,X52,X53,X54,X55,X56) )
      & ( r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)
        | esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) = X50
        | esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) = X51
        | esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) = X52
        | esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) = X53
        | esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) = X54
        | esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) = X55
        | esk1_8(X50,X51,X52,X53,X54,X55,X56,X57) = X56
        | X57 = k5_enumset1(X50,X51,X52,X53,X54,X55,X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).

fof(c_0_41,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30] : k6_enumset1(X24,X24,X25,X26,X27,X28,X29,X30) = k5_enumset1(X24,X25,X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_42,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_29])])).

cnf(c_0_43,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_45,plain,(
    ! [X64,X65] :
      ( ( ~ m1_subset_1(X64,k1_zfmisc_1(X65))
        | r1_tarski(X64,X65) )
      & ( ~ r1_tarski(X64,X65)
        | m1_subset_1(X64,k1_zfmisc_1(X65)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_46,plain,(
    ! [X66,X67] :
      ( ~ r2_hidden(X66,X67)
      | r1_tarski(k1_setfam_1(X67),X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X4,X5,X6,X7,X8,X9) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(X1,esk4_0,esk3_0),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X4,X5,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0)),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_39])).

cnf(c_0_54,plain,
    ( m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).

cnf(c_0_56,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_44,c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 21:02:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t38_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_2)).
% 0.12/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.37  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.12/0.37  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.12/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.37  fof(t81_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 0.12/0.37  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.12/0.37  fof(d5_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:(X8=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)<=>![X9]:(r2_hidden(X9,X8)<=>~(((((((X9!=X1&X9!=X2)&X9!=X3)&X9!=X4)&X9!=X5)&X9!=X6)&X9!=X7)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_enumset1)).
% 0.12/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.12/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.37  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.12/0.37  fof(c_0_14, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3)))))))), inference(assume_negation,[status(cth)],[t38_tops_2])).
% 0.12/0.37  fof(c_0_15, plain, ![X62, X63]:k1_setfam_1(k2_tarski(X62,X63))=k3_xboole_0(X62,X63), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.37  fof(c_0_16, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  fof(c_0_17, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&~m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk2_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.12/0.37  fof(c_0_18, plain, ![X68, X69]:(~l1_pre_topc(X68)|(~m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))|u1_struct_0(k1_pre_topc(X68,X69))=X69)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.12/0.37  fof(c_0_19, plain, ![X59, X60, X61]:(~m1_subset_1(X61,k1_zfmisc_1(X59))|k9_subset_1(X59,X60,X61)=k3_xboole_0(X60,X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.12/0.37  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  fof(c_0_22, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.37  fof(c_0_23, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.37  fof(c_0_24, plain, ![X19, X20, X21, X22, X23]:k4_enumset1(X19,X19,X20,X21,X22,X23)=k3_enumset1(X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.37  fof(c_0_25, plain, ![X31, X32, X33, X34, X35, X36]:k6_enumset1(X31,X31,X31,X32,X33,X34,X35,X36)=k4_enumset1(X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t81_enumset1])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk2_0,esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_27, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_30, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(X37))|k9_subset_1(X37,X38,X39)=k9_subset_1(X37,X39,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.12/0.37  cnf(c_0_31, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_32, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.37  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_36, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 0.12/0.37  cnf(c_0_38, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  cnf(c_0_39, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.12/0.37  fof(c_0_40, plain, ![X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57]:(((~r2_hidden(X48,X47)|(X48=X40|X48=X41|X48=X42|X48=X43|X48=X44|X48=X45|X48=X46)|X47!=k5_enumset1(X40,X41,X42,X43,X44,X45,X46))&(((((((X49!=X40|r2_hidden(X49,X47)|X47!=k5_enumset1(X40,X41,X42,X43,X44,X45,X46))&(X49!=X41|r2_hidden(X49,X47)|X47!=k5_enumset1(X40,X41,X42,X43,X44,X45,X46)))&(X49!=X42|r2_hidden(X49,X47)|X47!=k5_enumset1(X40,X41,X42,X43,X44,X45,X46)))&(X49!=X43|r2_hidden(X49,X47)|X47!=k5_enumset1(X40,X41,X42,X43,X44,X45,X46)))&(X49!=X44|r2_hidden(X49,X47)|X47!=k5_enumset1(X40,X41,X42,X43,X44,X45,X46)))&(X49!=X45|r2_hidden(X49,X47)|X47!=k5_enumset1(X40,X41,X42,X43,X44,X45,X46)))&(X49!=X46|r2_hidden(X49,X47)|X47!=k5_enumset1(X40,X41,X42,X43,X44,X45,X46))))&((((((((esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)!=X50|~r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k5_enumset1(X50,X51,X52,X53,X54,X55,X56))&(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)!=X51|~r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k5_enumset1(X50,X51,X52,X53,X54,X55,X56)))&(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)!=X52|~r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k5_enumset1(X50,X51,X52,X53,X54,X55,X56)))&(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)!=X53|~r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k5_enumset1(X50,X51,X52,X53,X54,X55,X56)))&(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)!=X54|~r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k5_enumset1(X50,X51,X52,X53,X54,X55,X56)))&(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)!=X55|~r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k5_enumset1(X50,X51,X52,X53,X54,X55,X56)))&(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)!=X56|~r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)|X57=k5_enumset1(X50,X51,X52,X53,X54,X55,X56)))&(r2_hidden(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57),X57)|(esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)=X50|esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)=X51|esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)=X52|esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)=X53|esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)=X54|esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)=X55|esk1_8(X50,X51,X52,X53,X54,X55,X56,X57)=X56)|X57=k5_enumset1(X50,X51,X52,X53,X54,X55,X56)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).
% 0.12/0.37  fof(c_0_41, plain, ![X24, X25, X26, X27, X28, X29, X30]:k6_enumset1(X24,X24,X25,X26,X27,X28,X29,X30)=k5_enumset1(X24,X25,X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk3_0),k1_zfmisc_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_29])])).
% 0.12/0.37  cnf(c_0_43, plain, (k9_subset_1(X1,X2,X3)=k9_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_39, c_0_39])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_45, plain, ![X64, X65]:((~m1_subset_1(X64,k1_zfmisc_1(X65))|r1_tarski(X64,X65))&(~r1_tarski(X64,X65)|m1_subset_1(X64,k1_zfmisc_1(X65)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.37  fof(c_0_46, plain, ![X66, X67]:(~r2_hidden(X66,X67)|r1_tarski(k1_setfam_1(X67),X66)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.12/0.37  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X4,X5,X6,X7,X8,X9)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.37  cnf(c_0_48, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (~m1_subset_1(k9_subset_1(X1,esk4_0,esk3_0),k1_zfmisc_1(esk4_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.12/0.37  cnf(c_0_50, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.37  cnf(c_0_51, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.37  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X4,X5,X6,X7,X8,X9)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (~m1_subset_1(k1_setfam_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0)),k1_zfmisc_1(esk4_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_39])).
% 0.12/0.37  cnf(c_0_54, plain, (m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X2))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.12/0.37  cnf(c_0_55, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_44, c_0_56]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 58
% 0.12/0.37  # Proof object clause steps            : 29
% 0.12/0.37  # Proof object formula steps           : 29
% 0.12/0.37  # Proof object conjectures             : 13
% 0.12/0.37  # Proof object clause conjectures      : 10
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 17
% 0.12/0.37  # Proof object initial formulas used   : 14
% 0.12/0.37  # Proof object generating inferences   : 7
% 0.12/0.37  # Proof object simplifying inferences  : 19
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 14
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 33
% 0.12/0.37  # Removed in clause preprocessing      : 7
% 0.12/0.37  # Initial clauses in saturation        : 26
% 0.12/0.37  # Processed clauses                    : 151
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 74
% 0.12/0.37  # ...remaining for further processing  : 77
% 0.12/0.37  # Other redundant clauses eliminated   : 22
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 234
% 0.12/0.37  # ...of the previous two non-trivial   : 217
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 218
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 22
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 42
% 0.12/0.37  #    Positive orientable unit clauses  : 9
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 5
% 0.12/0.37  #    Non-unit-clauses                  : 28
% 0.12/0.37  # Current number of unprocessed clauses: 118
% 0.12/0.37  # ...number of literals in the above   : 849
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 34
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 431
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 333
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 71
% 0.12/0.37  # Unit Clause-clause subsumption calls : 24
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 42
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 6021
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.033 s
% 0.12/0.37  # System time              : 0.007 s
% 0.12/0.37  # Total time               : 0.040 s
% 0.12/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
