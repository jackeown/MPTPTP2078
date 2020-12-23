%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 (  68 expanded)
%              Number of clauses        :   26 (  27 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  167 ( 216 expanded)
%              Number of equality atoms :   93 (  93 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t38_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

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

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(c_0_14,plain,(
    ! [X65,X66] : k1_setfam_1(k2_tarski(X65,X66)) = k3_xboole_0(X65,X66) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3)))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_tops_2])).

fof(c_0_17,plain,(
    ! [X67,X68] :
      ( ( ~ m1_subset_1(X67,k1_zfmisc_1(X68))
        | r1_tarski(X67,X68) )
      & ( ~ r1_tarski(X67,X68)
        | m1_subset_1(X67,k1_zfmisc_1(X68)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_18,plain,(
    ! [X69,X70] :
      ( ~ r2_hidden(X69,X70)
      | r1_tarski(k1_setfam_1(X70),X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

fof(c_0_19,plain,(
    ! [X62,X63,X64] :
      ( ~ m1_subset_1(X64,k1_zfmisc_1(X62))
      | k9_subset_1(X62,X63,X64) = k3_xboole_0(X63,X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X16,X17,X18,X19] : k3_enumset1(X16,X16,X17,X18,X19) = k2_enumset1(X16,X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X20,X21,X22,X23,X24] : k4_enumset1(X20,X20,X21,X22,X23,X24) = k3_enumset1(X20,X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X25,X26,X27,X28,X29,X30] : k5_enumset1(X25,X25,X26,X27,X28,X29,X30) = k4_enumset1(X25,X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_26,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37] : k6_enumset1(X31,X31,X32,X33,X34,X35,X36,X37) = k5_enumset1(X31,X32,X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ~ m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk2_0,esk4_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_28,plain,(
    ! [X71,X72] :
      ( ~ l1_pre_topc(X71)
      | ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))
      | u1_struct_0(k1_pre_topc(X71,X72)) = X72 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

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
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_38,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60] :
      ( ( ~ r2_hidden(X50,X49)
        | X50 = X41
        | X50 = X42
        | X50 = X43
        | X50 = X44
        | X50 = X45
        | X50 = X46
        | X50 = X47
        | X50 = X48
        | X49 != k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X41
        | r2_hidden(X51,X49)
        | X49 != k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X42
        | r2_hidden(X51,X49)
        | X49 != k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X43
        | r2_hidden(X51,X49)
        | X49 != k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X44
        | r2_hidden(X51,X49)
        | X49 != k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X45
        | r2_hidden(X51,X49)
        | X49 != k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X46
        | r2_hidden(X51,X49)
        | X49 != k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X47
        | r2_hidden(X51,X49)
        | X49 != k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( X51 != X48
        | r2_hidden(X51,X49)
        | X49 != k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) != X52
        | ~ r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)
        | X60 = k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) != X53
        | ~ r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)
        | X60 = k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) != X54
        | ~ r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)
        | X60 = k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) != X55
        | ~ r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)
        | X60 = k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) != X56
        | ~ r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)
        | X60 = k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) != X57
        | ~ r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)
        | X60 = k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) != X58
        | ~ r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)
        | X60 = k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) != X59
        | ~ r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)
        | X60 = k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) )
      & ( r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)
        | esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) = X52
        | esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) = X53
        | esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) = X54
        | esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) = X55
        | esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) = X56
        | esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) = X57
        | esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) = X58
        | esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60) = X59
        | X60 = k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk2_0,esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_43,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X38))
      | k9_subset_1(X38,X39,X40) = k9_subset_1(X38,X40,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_44,plain,
    ( m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_45,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X2,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_48,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ r2_hidden(X4,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X1,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_42])])).

cnf(c_0_52,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:24:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.050 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.40  fof(t38_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_2)).
% 0.19/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.40  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.19/0.40  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.19/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.40  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.40  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.19/0.40  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 0.19/0.40  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.19/0.40  fof(c_0_14, plain, ![X65, X66]:k1_setfam_1(k2_tarski(X65,X66))=k3_xboole_0(X65,X66), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.40  fof(c_0_15, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.40  fof(c_0_16, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3)))))))), inference(assume_negation,[status(cth)],[t38_tops_2])).
% 0.19/0.40  fof(c_0_17, plain, ![X67, X68]:((~m1_subset_1(X67,k1_zfmisc_1(X68))|r1_tarski(X67,X68))&(~r1_tarski(X67,X68)|m1_subset_1(X67,k1_zfmisc_1(X68)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.40  fof(c_0_18, plain, ![X69, X70]:(~r2_hidden(X69,X70)|r1_tarski(k1_setfam_1(X70),X69)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.19/0.40  fof(c_0_19, plain, ![X62, X63, X64]:(~m1_subset_1(X64,k1_zfmisc_1(X62))|k9_subset_1(X62,X63,X64)=k3_xboole_0(X63,X64)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.19/0.40  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  fof(c_0_22, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.40  fof(c_0_23, plain, ![X16, X17, X18, X19]:k3_enumset1(X16,X16,X17,X18,X19)=k2_enumset1(X16,X17,X18,X19), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.40  fof(c_0_24, plain, ![X20, X21, X22, X23, X24]:k4_enumset1(X20,X20,X21,X22,X23,X24)=k3_enumset1(X20,X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.40  fof(c_0_25, plain, ![X25, X26, X27, X28, X29, X30]:k5_enumset1(X25,X25,X26,X27,X28,X29,X30)=k4_enumset1(X25,X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.40  fof(c_0_26, plain, ![X31, X32, X33, X34, X35, X36, X37]:k6_enumset1(X31,X31,X32,X33,X34,X35,X36,X37)=k5_enumset1(X31,X32,X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.40  fof(c_0_27, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&~m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk2_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.19/0.40  fof(c_0_28, plain, ![X71, X72]:(~l1_pre_topc(X71)|(~m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))|u1_struct_0(k1_pre_topc(X71,X72))=X72)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.19/0.40  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_30, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_31, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_32, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.40  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.40  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_37, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  fof(c_0_38, plain, ![X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60]:(((~r2_hidden(X50,X49)|(X50=X41|X50=X42|X50=X43|X50=X44|X50=X45|X50=X46|X50=X47|X50=X48)|X49!=k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48))&((((((((X51!=X41|r2_hidden(X51,X49)|X49!=k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48))&(X51!=X42|r2_hidden(X51,X49)|X49!=k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X43|r2_hidden(X51,X49)|X49!=k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X44|r2_hidden(X51,X49)|X49!=k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X45|r2_hidden(X51,X49)|X49!=k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X46|r2_hidden(X51,X49)|X49!=k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X47|r2_hidden(X51,X49)|X49!=k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48)))&(X51!=X48|r2_hidden(X51,X49)|X49!=k6_enumset1(X41,X42,X43,X44,X45,X46,X47,X48))))&(((((((((esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)!=X52|~r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)|X60=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59))&(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)!=X53|~r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)|X60=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)!=X54|~r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)|X60=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)!=X55|~r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)|X60=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)!=X56|~r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)|X60=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)!=X57|~r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)|X60=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)!=X58|~r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)|X60=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)!=X59|~r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)|X60=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))&(r2_hidden(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60),X60)|(esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)=X52|esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)=X53|esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)=X54|esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)=X55|esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)=X56|esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)=X57|esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)=X58|esk1_9(X52,X53,X54,X55,X56,X57,X58,X59,X60)=X59)|X60=k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk2_0,esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_40, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  fof(c_0_43, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(X38))|k9_subset_1(X38,X39,X40)=k9_subset_1(X38,X40,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.19/0.40  cnf(c_0_44, plain, (m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X2))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.40  cnf(c_0_45, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.19/0.40  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X2,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])])).
% 0.19/0.40  cnf(c_0_48, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.40  cnf(c_0_49, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~r2_hidden(X4,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.40  cnf(c_0_50, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X1,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk3_0),k1_zfmisc_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_42])])).
% 0.19/0.40  cnf(c_0_52, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 55
% 0.19/0.40  # Proof object clause steps            : 26
% 0.19/0.40  # Proof object formula steps           : 29
% 0.19/0.40  # Proof object conjectures             : 10
% 0.19/0.40  # Proof object clause conjectures      : 7
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 17
% 0.19/0.40  # Proof object initial formulas used   : 14
% 0.19/0.40  # Proof object generating inferences   : 6
% 0.19/0.40  # Proof object simplifying inferences  : 16
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 14
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 35
% 0.19/0.40  # Removed in clause preprocessing      : 7
% 0.19/0.40  # Initial clauses in saturation        : 28
% 0.19/0.40  # Processed clauses                    : 128
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 46
% 0.19/0.40  # ...remaining for further processing  : 82
% 0.19/0.40  # Other redundant clauses eliminated   : 17
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 0
% 0.19/0.40  # Generated clauses                    : 186
% 0.19/0.40  # ...of the previous two non-trivial   : 165
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 177
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 17
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 45
% 0.19/0.40  #    Positive orientable unit clauses  : 11
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 4
% 0.19/0.40  #    Non-unit-clauses                  : 30
% 0.19/0.40  # Current number of unprocessed clauses: 93
% 0.19/0.40  # ...number of literals in the above   : 356
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 35
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 352
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 327
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 43
% 0.19/0.40  # Unit Clause-clause subsumption calls : 4
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 56
% 0.19/0.40  # BW rewrite match successes           : 0
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 4818
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.058 s
% 0.19/0.40  # System time              : 0.006 s
% 0.19/0.40  # Total time               : 0.064 s
% 0.19/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
