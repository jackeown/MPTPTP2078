%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:57 EST 2020

% Result     : Theorem 44.27s
% Output     : CNFRefutation 44.27s
% Verified   : 
% Statistics : Number of formulae       :  171 (1050 expanded)
%              Number of clauses        :  132 ( 521 expanded)
%              Number of leaves         :   19 ( 258 expanded)
%              Depth                    :   31
%              Number of atoms          :  415 (2324 expanded)
%              Number of equality atoms :   25 ( 422 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t50_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(c_0_19,plain,(
    ! [X38] : m1_subset_1(k2_subset_1(X38),k1_zfmisc_1(X38)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_20,plain,(
    ! [X37] : k2_subset_1(X37) = X37 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_21,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ( ~ r2_hidden(X32,X31)
        | r1_tarski(X32,X30)
        | X31 != k1_zfmisc_1(X30) )
      & ( ~ r1_tarski(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k1_zfmisc_1(X30) )
      & ( ~ r2_hidden(esk2_2(X34,X35),X35)
        | ~ r1_tarski(esk2_2(X34,X35),X34)
        | X35 = k1_zfmisc_1(X34) )
      & ( r2_hidden(esk2_2(X34,X35),X35)
        | r1_tarski(esk2_2(X34,X35),X34)
        | X35 = k1_zfmisc_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_22,plain,(
    ! [X44,X45] :
      ( ( ~ m1_subset_1(X44,k1_zfmisc_1(X45))
        | r1_tarski(X44,X45) )
      & ( ~ r1_tarski(X44,X45)
        | m1_subset_1(X44,k1_zfmisc_1(X45)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(k2_xboole_0(X12,X13),X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_30,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_31,plain,(
    ! [X46,X47,X48] :
      ( ~ r2_hidden(X46,X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(X48))
      | m1_subset_1(X46,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X3),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k2_xboole_0(k1_zfmisc_1(X2),X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_33])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X3),X4),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k2_xboole_0(X2,X3)))
    | ~ r1_tarski(esk1_2(X1,k1_zfmisc_1(k2_xboole_0(X2,X3))),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X3),X4)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X3),X4),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_45])).

fof(c_0_56,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_57,plain,(
    ! [X42,X43] : k1_setfam_1(k2_tarski(X42,X43)) = k3_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(k2_xboole_0(X3,X4)),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X3),X4)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_36])).

fof(c_0_60,plain,(
    ! [X25,X26] : r1_xboole_0(k4_xboole_0(X25,X26),X26) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_63,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | k7_subset_1(X39,X40,X41) = k4_xboole_0(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X3),X2)
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_58,c_0_36])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(k2_xboole_0(X3,X4)),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_54])).

fof(c_0_66,plain,(
    ! [X22,X23,X24] :
      ( ( r1_xboole_0(X22,k2_xboole_0(X23,X24))
        | ~ r1_xboole_0(X22,X23)
        | ~ r1_xboole_0(X22,X24) )
      & ( r1_xboole_0(X22,X23)
        | ~ r1_xboole_0(X22,k2_xboole_0(X23,X24)) )
      & ( r1_xboole_0(X22,X24)
        | ~ r1_xboole_0(X22,k2_xboole_0(X23,X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_67,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_35])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X3),X2)
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_65,c_0_36])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X2) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_68])).

cnf(c_0_75,plain,
    ( m1_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(k1_zfmisc_1(k2_xboole_0(X1,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_54])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_35])).

fof(c_0_77,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_78,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_72,c_0_36])).

cnf(c_0_79,plain,
    ( r1_xboole_0(k7_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,plain,
    ( m1_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_35])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(k2_xboole_0(X3,X4),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_76,c_0_47])).

cnf(c_0_82,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,plain,
    ( r1_xboole_0(k7_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_80])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_40])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_81,c_0_36])).

cnf(c_0_87,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_82,c_0_68])).

fof(c_0_88,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_tops_1])).

cnf(c_0_89,plain,
    ( r1_xboole_0(k7_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X4,X5)
    | ~ r1_tarski(X5,X3) ),
    inference(spm,[status(thm)],[c_0_78,c_0_83])).

cnf(c_0_90,plain,
    ( m1_subset_1(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X4,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_37,c_0_84])).

cnf(c_0_91,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_35])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4))))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

fof(c_0_93,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ~ r1_tarski(k1_tops_1(esk3_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0)),k7_subset_1(u1_struct_0(esk3_0),k1_tops_1(esk3_0,esk4_0),k1_tops_1(esk3_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_88])])])).

cnf(c_0_94,plain,
    ( r1_xboole_0(k7_subset_1(X1,X1,X2),X3)
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_29])).

cnf(c_0_95,plain,
    ( m1_subset_1(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_35])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_99,plain,
    ( r1_xboole_0(k7_subset_1(X1,X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_94,c_0_35])).

cnf(c_0_100,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X3,X4),X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_36])).

cnf(c_0_101,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k7_subset_1(X3,X2,X4)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_74])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_97])).

fof(c_0_103,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_xboole_0(X20,X21)
      | r1_xboole_0(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_104,plain,
    ( r1_xboole_0(k7_subset_1(X1,X1,X2),X3)
    | ~ r1_tarski(k2_xboole_0(X4,X3),X2) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

fof(c_0_105,plain,(
    ! [X49,X50] :
      ( ~ l1_pre_topc(X49)
      | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
      | r1_tarski(k1_tops_1(X49,X50),X50) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_106,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_100,c_0_36])).

cnf(c_0_107,plain,
    ( r2_hidden(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_35])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_102])).

cnf(c_0_109,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_110,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_111,plain,
    ( r1_xboole_0(k7_subset_1(X1,X1,k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_104,c_0_35])).

cnf(c_0_112,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_87])).

cnf(c_0_113,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_115,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_116,plain,
    ( m1_subset_1(k7_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k1_zfmisc_1(X2),X5)
    | ~ r1_tarski(X5,X4) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk1_2(X1,k1_zfmisc_1(u1_struct_0(esk3_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_108])).

cnf(c_0_118,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X4,X3)
    | ~ r1_xboole_0(X4,X2)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_119,plain,
    ( r1_xboole_0(k7_subset_1(X1,X1,X2),X2)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_111,c_0_36])).

cnf(c_0_120,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3))),X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_87])).

cnf(c_0_121,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_47])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])])).

cnf(c_0_123,plain,
    ( m1_subset_1(k7_subset_1(X1,X1,X2),X3)
    | ~ r1_tarski(k1_zfmisc_1(X1),X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_116,c_0_29])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_117,c_0_52])).

fof(c_0_125,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(X27,X28)
      | ~ r1_xboole_0(X27,X29)
      | r1_tarski(X27,k4_xboole_0(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_126,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ r1_xboole_0(k7_subset_1(X5,X4,X3),X2)
    | ~ r1_tarski(X1,k7_subset_1(X5,X4,X3)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_79])).

cnf(c_0_127,plain,
    ( r1_xboole_0(k7_subset_1(X1,X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk5_0),k2_xboole_0(X1,X2))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(k7_subset_1(esk4_0,esk4_0,X1),X2)
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),X2) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_130,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk3_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0)),k7_subset_1(u1_struct_0(esk3_0),k1_tops_1(esk3_0,esk4_0),k1_tops_1(esk3_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_131,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_74])).

cnf(c_0_132,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_125])).

cnf(c_0_133,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X2))
    | ~ r1_tarski(X1,k7_subset_1(X3,X3,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_29])])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk5_0),X1)
    | ~ r1_tarski(esk5_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_128,c_0_36])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(k7_subset_1(esk4_0,esk4_0,X1),X2)
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_129])).

cnf(c_0_136,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k1_tops_1(esk3_0,k7_subset_1(X1,esk4_0,esk5_0)),k7_subset_1(u1_struct_0(esk3_0),k1_tops_1(esk3_0,esk4_0),k1_tops_1(esk3_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_97])])).

cnf(c_0_137,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[c_0_132,c_0_68])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X2,esk4_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_108])).

cnf(c_0_139,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_97]),c_0_115])])).

cnf(c_0_140,plain,
    ( r1_xboole_0(k7_subset_1(X1,X1,X2),k2_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_35])).

cnf(c_0_141,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk5_0),X1)
    | ~ r1_tarski(k2_xboole_0(esk5_0,X2),X1) ),
    inference(spm,[status(thm)],[c_0_134,c_0_40])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k7_subset_1(esk4_0,esk4_0,X3)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_135])).

cnf(c_0_143,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k1_tops_1(esk3_0,k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,esk5_0)))),k7_subset_1(u1_struct_0(esk3_0),k1_tops_1(esk3_0,esk4_0),k1_tops_1(esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_136,c_0_74])).

cnf(c_0_144,plain,
    ( r1_tarski(X1,k7_subset_1(X2,X3,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,X4)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_137,c_0_74])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_146,plain,
    ( r1_xboole_0(k7_subset_1(X1,X1,X2),X3)
    | ~ r1_tarski(X3,k2_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_140])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk5_0),k2_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_35])).

cnf(c_0_148,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,k7_subset_1(esk4_0,esk4_0,X2)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_35])).

fof(c_0_149,plain,(
    ! [X51,X52,X53] :
      ( ~ l1_pre_topc(X51)
      | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))
      | ~ r1_tarski(X52,X53)
      | r1_tarski(k1_tops_1(X51,X52),k1_tops_1(X51,X53)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_150,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k1_tops_1(esk3_0,k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,esk5_0)))),k1_tops_1(esk3_0,esk5_0))
    | ~ r1_tarski(k1_tops_1(esk3_0,k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,esk5_0)))),k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_143,c_0_144])).

cnf(c_0_151,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_145,c_0_35])).

cnf(c_0_152,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(X1,X1,esk5_0),k1_tops_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_153,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_38])).

cnf(c_0_154,negated_conjecture,
    ( r1_tarski(k7_subset_1(esk4_0,esk4_0,X1),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_148,c_0_35])).

cnf(c_0_155,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_149])).

cnf(c_0_156,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X3),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_33])).

cnf(c_0_157,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k1_tops_1(esk3_0,k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,esk5_0)))),k1_tops_1(esk3_0,esk5_0))
    | ~ r1_tarski(k1_tops_1(esk3_0,k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,esk5_0)))),k1_tops_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_38]),c_0_151])])).

cnf(c_0_158,negated_conjecture,
    ( r1_xboole_0(X1,k1_tops_1(esk3_0,esk5_0))
    | ~ r1_tarski(X1,k7_subset_1(X2,X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_152])).

cnf(c_0_159,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,k7_subset_1(esk4_0,esk4_0,X1)),k7_subset_1(esk4_0,esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_115])])).

cnf(c_0_160,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k1_tops_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_155])).

cnf(c_0_161,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_156,c_0_124])).

cnf(c_0_162,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k1_tops_1(esk3_0,k7_subset_1(X2,esk4_0,esk5_0)),k1_tops_1(esk3_0,esk5_0))
    | ~ r1_tarski(k1_tops_1(esk3_0,k7_subset_1(X2,esk4_0,esk5_0)),k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_157,c_0_74])).

cnf(c_0_163,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(esk3_0,k7_subset_1(esk4_0,esk4_0,esk5_0)),k1_tops_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_158,c_0_159])).

cnf(c_0_164,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ r1_tarski(X1,k1_tops_1(esk3_0,X2))
    | ~ r1_tarski(X2,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_97]),c_0_115])]),c_0_161])).

cnf(c_0_165,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k1_tops_1(esk3_0,k7_subset_1(esk4_0,esk4_0,esk5_0)),k1_tops_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_163]),c_0_29])])).

cnf(c_0_166,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,X1),k1_tops_1(esk3_0,esk4_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_164,c_0_35])).

cnf(c_0_167,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k7_subset_1(esk4_0,esk4_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_165,c_0_166])).

cnf(c_0_168,plain,
    ( r1_tarski(k7_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_74])).

cnf(c_0_169,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_168]),c_0_29])])).

cnf(c_0_170,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_97,c_0_169]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:15:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 44.27/44.50  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 44.27/44.50  # and selection function SelectComplexExceptUniqMaxHorn.
% 44.27/44.50  #
% 44.27/44.50  # Preprocessing time       : 0.028 s
% 44.27/44.50  # Presaturation interreduction done
% 44.27/44.50  
% 44.27/44.50  # Proof found!
% 44.27/44.50  # SZS status Theorem
% 44.27/44.50  # SZS output start CNFRefutation
% 44.27/44.50  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 44.27/44.50  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 44.27/44.50  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 44.27/44.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 44.27/44.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 44.27/44.50  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 44.27/44.50  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 44.27/44.50  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 44.27/44.50  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 44.27/44.50  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 44.27/44.50  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 44.27/44.50  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 44.27/44.50  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 44.27/44.50  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 44.27/44.50  fof(t50_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tops_1)).
% 44.27/44.50  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 44.27/44.51  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 44.27/44.51  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 44.27/44.51  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 44.27/44.51  fof(c_0_19, plain, ![X38]:m1_subset_1(k2_subset_1(X38),k1_zfmisc_1(X38)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 44.27/44.51  fof(c_0_20, plain, ![X37]:k2_subset_1(X37)=X37, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 44.27/44.51  fof(c_0_21, plain, ![X30, X31, X32, X33, X34, X35]:(((~r2_hidden(X32,X31)|r1_tarski(X32,X30)|X31!=k1_zfmisc_1(X30))&(~r1_tarski(X33,X30)|r2_hidden(X33,X31)|X31!=k1_zfmisc_1(X30)))&((~r2_hidden(esk2_2(X34,X35),X35)|~r1_tarski(esk2_2(X34,X35),X34)|X35=k1_zfmisc_1(X34))&(r2_hidden(esk2_2(X34,X35),X35)|r1_tarski(esk2_2(X34,X35),X34)|X35=k1_zfmisc_1(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 44.27/44.51  fof(c_0_22, plain, ![X44, X45]:((~m1_subset_1(X44,k1_zfmisc_1(X45))|r1_tarski(X44,X45))&(~r1_tarski(X44,X45)|m1_subset_1(X44,k1_zfmisc_1(X45)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 44.27/44.51  cnf(c_0_23, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 44.27/44.51  cnf(c_0_24, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 44.27/44.51  fof(c_0_25, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 44.27/44.51  cnf(c_0_26, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 44.27/44.51  fof(c_0_27, plain, ![X12, X13, X14]:(~r1_tarski(k2_xboole_0(X12,X13),X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 44.27/44.51  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 44.27/44.51  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 44.27/44.51  fof(c_0_30, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 44.27/44.51  fof(c_0_31, plain, ![X46, X47, X48]:(~r2_hidden(X46,X47)|~m1_subset_1(X47,k1_zfmisc_1(X48))|m1_subset_1(X46,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 44.27/44.51  cnf(c_0_32, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 44.27/44.51  cnf(c_0_33, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_26])).
% 44.27/44.51  cnf(c_0_34, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 44.27/44.51  cnf(c_0_35, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 44.27/44.51  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 44.27/44.51  cnf(c_0_37, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 44.27/44.51  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 44.27/44.51  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_zfmisc_1(X3),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 44.27/44.51  cnf(c_0_40, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 44.27/44.51  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 44.27/44.51  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 44.27/44.51  cnf(c_0_43, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 44.27/44.51  cnf(c_0_44, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 44.27/44.51  cnf(c_0_45, plain, (r2_hidden(X1,k2_xboole_0(k1_zfmisc_1(X2),X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 44.27/44.51  cnf(c_0_46, plain, (r1_tarski(X1,k1_zfmisc_1(X2))|~r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X2)), inference(spm,[status(thm)],[c_0_41, c_0_33])).
% 44.27/44.51  cnf(c_0_47, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_40])).
% 44.27/44.51  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_43])).
% 44.27/44.51  cnf(c_0_49, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 44.27/44.51  cnf(c_0_50, plain, (m1_subset_1(X1,X2)|~r1_tarski(k2_xboole_0(k1_zfmisc_1(X3),X4),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 44.27/44.51  cnf(c_0_51, plain, (r1_tarski(X1,k1_zfmisc_1(k2_xboole_0(X2,X3)))|~r1_tarski(esk1_2(X1,k1_zfmisc_1(k2_xboole_0(X2,X3))),X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 44.27/44.51  cnf(c_0_52, plain, (r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)|r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 44.27/44.51  cnf(c_0_53, plain, (m1_subset_1(X1,X2)|~r1_tarski(k1_zfmisc_1(X3),X4)|~r1_tarski(X4,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_50, c_0_36])).
% 44.27/44.51  cnf(c_0_54, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 44.27/44.51  cnf(c_0_55, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(k1_zfmisc_1(X3),X4),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_32, c_0_45])).
% 44.27/44.51  fof(c_0_56, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 44.27/44.51  fof(c_0_57, plain, ![X42, X43]:k1_setfam_1(k2_tarski(X42,X43))=k3_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 44.27/44.51  cnf(c_0_58, plain, (m1_subset_1(X1,X2)|~r1_tarski(k1_zfmisc_1(k2_xboole_0(X3,X4)),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 44.27/44.51  cnf(c_0_59, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_zfmisc_1(X3),X4)|~r1_tarski(X4,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_55, c_0_36])).
% 44.27/44.51  fof(c_0_60, plain, ![X25, X26]:r1_xboole_0(k4_xboole_0(X25,X26),X26), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 44.27/44.51  cnf(c_0_61, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 44.27/44.51  cnf(c_0_62, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 44.27/44.51  fof(c_0_63, plain, ![X39, X40, X41]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|k7_subset_1(X39,X40,X41)=k4_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 44.27/44.51  cnf(c_0_64, plain, (m1_subset_1(X1,X2)|~r1_tarski(k1_zfmisc_1(X3),X2)|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_58, c_0_36])).
% 44.27/44.51  cnf(c_0_65, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_zfmisc_1(k2_xboole_0(X3,X4)),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_59, c_0_54])).
% 44.27/44.51  fof(c_0_66, plain, ![X22, X23, X24]:((r1_xboole_0(X22,k2_xboole_0(X23,X24))|~r1_xboole_0(X22,X23)|~r1_xboole_0(X22,X24))&((r1_xboole_0(X22,X23)|~r1_xboole_0(X22,k2_xboole_0(X23,X24)))&(r1_xboole_0(X22,X24)|~r1_xboole_0(X22,k2_xboole_0(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 44.27/44.51  cnf(c_0_67, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 44.27/44.51  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 44.27/44.51  cnf(c_0_69, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 44.27/44.51  cnf(c_0_70, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_64, c_0_35])).
% 44.27/44.51  cnf(c_0_71, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_zfmisc_1(X3),X2)|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_65, c_0_36])).
% 44.27/44.51  cnf(c_0_72, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 44.27/44.51  cnf(c_0_73, plain, (r1_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X2)), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 44.27/44.51  cnf(c_0_74, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_69, c_0_68])).
% 44.27/44.51  cnf(c_0_75, plain, (m1_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(k1_zfmisc_1(k2_xboole_0(X1,X3)),X2)), inference(spm,[status(thm)],[c_0_70, c_0_54])).
% 44.27/44.51  cnf(c_0_76, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_71, c_0_35])).
% 44.27/44.51  fof(c_0_77, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 44.27/44.51  cnf(c_0_78, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_72, c_0_36])).
% 44.27/44.51  cnf(c_0_79, plain, (r1_xboole_0(k7_subset_1(X1,X2,X3),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 44.27/44.51  cnf(c_0_80, plain, (m1_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_75, c_0_35])).
% 44.27/44.51  cnf(c_0_81, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(k2_xboole_0(X3,X4),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_76, c_0_47])).
% 44.27/44.51  cnf(c_0_82, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 44.27/44.51  cnf(c_0_83, plain, (r1_xboole_0(k7_subset_1(X1,X2,X3),X4)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 44.27/44.51  cnf(c_0_84, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3)))|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_80])).
% 44.27/44.51  cnf(c_0_85, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(k2_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_76, c_0_40])).
% 44.27/44.51  cnf(c_0_86, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X3,X2)|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_81, c_0_36])).
% 44.27/44.51  cnf(c_0_87, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_82, c_0_68])).
% 44.27/44.51  fof(c_0_88, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t50_tops_1])).
% 44.27/44.51  cnf(c_0_89, plain, (r1_xboole_0(k7_subset_1(X1,X2,X3),X4)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X4,X5)|~r1_tarski(X5,X3)), inference(spm,[status(thm)],[c_0_78, c_0_83])).
% 44.27/44.51  cnf(c_0_90, plain, (m1_subset_1(X1,k2_xboole_0(X2,X3))|~r2_hidden(X4,k1_zfmisc_1(X2))|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_37, c_0_84])).
% 44.27/44.51  cnf(c_0_91, plain, (r2_hidden(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_85, c_0_35])).
% 44.27/44.51  cnf(c_0_92, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X3,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4))))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 44.27/44.51  fof(c_0_93, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&~r1_tarski(k1_tops_1(esk3_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0)),k7_subset_1(u1_struct_0(esk3_0),k1_tops_1(esk3_0,esk4_0),k1_tops_1(esk3_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_88])])])).
% 44.27/44.51  cnf(c_0_94, plain, (r1_xboole_0(k7_subset_1(X1,X1,X2),X3)|~r1_tarski(X3,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_89, c_0_29])).
% 44.27/44.51  cnf(c_0_95, plain, (m1_subset_1(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 44.27/44.51  cnf(c_0_96, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))), inference(spm,[status(thm)],[c_0_92, c_0_35])).
% 44.27/44.51  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 44.27/44.51  cnf(c_0_98, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 44.27/44.51  cnf(c_0_99, plain, (r1_xboole_0(k7_subset_1(X1,X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_94, c_0_35])).
% 44.27/44.51  cnf(c_0_100, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(k2_xboole_0(X3,X4),X2)), inference(spm,[status(thm)],[c_0_95, c_0_36])).
% 44.27/44.51  cnf(c_0_101, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k7_subset_1(X3,X2,X4))), inference(spm,[status(thm)],[c_0_96, c_0_74])).
% 44.27/44.51  cnf(c_0_102, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_97])).
% 44.27/44.51  fof(c_0_103, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_xboole_0(X20,X21)|r1_xboole_0(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 44.27/44.51  cnf(c_0_104, plain, (r1_xboole_0(k7_subset_1(X1,X1,X2),X3)|~r1_tarski(k2_xboole_0(X4,X3),X2)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 44.27/44.51  fof(c_0_105, plain, ![X49, X50]:(~l1_pre_topc(X49)|(~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))|r1_tarski(k1_tops_1(X49,X50),X50))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 44.27/44.51  cnf(c_0_106, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X4,X2)|~r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_100, c_0_36])).
% 44.27/44.51  cnf(c_0_107, plain, (r2_hidden(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_101, c_0_35])).
% 44.27/44.51  cnf(c_0_108, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_102])).
% 44.27/44.51  cnf(c_0_109, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 44.27/44.51  cnf(c_0_110, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 44.27/44.51  cnf(c_0_111, plain, (r1_xboole_0(k7_subset_1(X1,X1,k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_104, c_0_35])).
% 44.27/44.51  cnf(c_0_112, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))), inference(spm,[status(thm)],[c_0_42, c_0_87])).
% 44.27/44.51  cnf(c_0_113, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 44.27/44.51  cnf(c_0_114, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 44.27/44.51  cnf(c_0_115, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 44.27/44.51  cnf(c_0_116, plain, (m1_subset_1(k7_subset_1(X1,X2,X3),X4)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k1_zfmisc_1(X2),X5)|~r1_tarski(X5,X4)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 44.27/44.51  cnf(c_0_117, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk1_2(X1,k1_zfmisc_1(u1_struct_0(esk3_0))),esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_108])).
% 44.27/44.51  cnf(c_0_118, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X4,X3)|~r1_xboole_0(X4,X2)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 44.27/44.51  cnf(c_0_119, plain, (r1_xboole_0(k7_subset_1(X1,X1,X2),X2)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_111, c_0_36])).
% 44.27/44.51  cnf(c_0_120, plain, (r1_tarski(k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3))),X1)), inference(spm,[status(thm)],[c_0_112, c_0_87])).
% 44.27/44.51  cnf(c_0_121, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_42, c_0_47])).
% 44.27/44.51  cnf(c_0_122, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])])).
% 44.27/44.51  cnf(c_0_123, plain, (m1_subset_1(k7_subset_1(X1,X1,X2),X3)|~r1_tarski(k1_zfmisc_1(X1),X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_116, c_0_29])).
% 44.27/44.51  cnf(c_0_124, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_117, c_0_52])).
% 44.27/44.51  fof(c_0_125, plain, ![X27, X28, X29]:(~r1_tarski(X27,X28)|~r1_xboole_0(X27,X29)|r1_tarski(X27,k4_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 44.27/44.51  cnf(c_0_126, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(X5))|~r1_xboole_0(k7_subset_1(X5,X4,X3),X2)|~r1_tarski(X1,k7_subset_1(X5,X4,X3))), inference(spm,[status(thm)],[c_0_118, c_0_79])).
% 44.27/44.51  cnf(c_0_127, plain, (r1_xboole_0(k7_subset_1(X1,X1,X2),X2)), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 44.27/44.51  cnf(c_0_128, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk5_0),k2_xboole_0(X1,X2))|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 44.27/44.51  cnf(c_0_129, negated_conjecture, (m1_subset_1(k7_subset_1(esk4_0,esk4_0,X1),X2)|~r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),X2)), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 44.27/44.51  cnf(c_0_130, negated_conjecture, (~r1_tarski(k1_tops_1(esk3_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0)),k7_subset_1(u1_struct_0(esk3_0),k1_tops_1(esk3_0,esk4_0),k1_tops_1(esk3_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 44.27/44.51  cnf(c_0_131, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_74, c_0_74])).
% 44.27/44.51  cnf(c_0_132, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_125])).
% 44.27/44.51  cnf(c_0_133, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X2))|~r1_tarski(X1,k7_subset_1(X3,X3,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_29])])).
% 44.27/44.51  cnf(c_0_134, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk5_0),X1)|~r1_tarski(esk5_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_128, c_0_36])).
% 44.27/44.51  cnf(c_0_135, negated_conjecture, (r1_tarski(k7_subset_1(esk4_0,esk4_0,X1),X2)|~r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_28, c_0_129])).
% 44.27/44.51  cnf(c_0_136, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~r1_tarski(k1_tops_1(esk3_0,k7_subset_1(X1,esk4_0,esk5_0)),k7_subset_1(u1_struct_0(esk3_0),k1_tops_1(esk3_0,esk4_0),k1_tops_1(esk3_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_97])])).
% 44.27/44.51  cnf(c_0_137, plain, (r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[c_0_132, c_0_68])).
% 44.27/44.51  cnf(c_0_138, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X2,esk4_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_108])).
% 44.27/44.51  cnf(c_0_139, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_97]), c_0_115])])).
% 44.27/44.51  cnf(c_0_140, plain, (r1_xboole_0(k7_subset_1(X1,X1,X2),k2_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_133, c_0_35])).
% 44.27/44.51  cnf(c_0_141, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk5_0),X1)|~r1_tarski(k2_xboole_0(esk5_0,X2),X1)), inference(spm,[status(thm)],[c_0_134, c_0_40])).
% 44.27/44.51  cnf(c_0_142, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),k1_zfmisc_1(X2))|~r1_tarski(X1,k7_subset_1(esk4_0,esk4_0,X3))), inference(spm,[status(thm)],[c_0_42, c_0_135])).
% 44.27/44.51  cnf(c_0_143, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~r1_tarski(k1_tops_1(esk3_0,k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,esk5_0)))),k7_subset_1(u1_struct_0(esk3_0),k1_tops_1(esk3_0,esk4_0),k1_tops_1(esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_136, c_0_74])).
% 44.27/44.51  cnf(c_0_144, plain, (r1_tarski(X1,k7_subset_1(X2,X3,X4))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X1,X4)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_137, c_0_74])).
% 44.27/44.51  cnf(c_0_145, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 44.27/44.51  cnf(c_0_146, plain, (r1_xboole_0(k7_subset_1(X1,X1,X2),X3)|~r1_tarski(X3,k2_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_78, c_0_140])).
% 44.27/44.51  cnf(c_0_147, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk5_0),k2_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_141, c_0_35])).
% 44.27/44.51  cnf(c_0_148, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,k7_subset_1(esk4_0,esk4_0,X2))), inference(spm,[status(thm)],[c_0_142, c_0_35])).
% 44.27/44.51  fof(c_0_149, plain, ![X51, X52, X53]:(~l1_pre_topc(X51)|(~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))|(~r1_tarski(X52,X53)|r1_tarski(k1_tops_1(X51,X52),k1_tops_1(X51,X53)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 44.27/44.51  cnf(c_0_150, negated_conjecture, (~m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~r1_xboole_0(k1_tops_1(esk3_0,k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,esk5_0)))),k1_tops_1(esk3_0,esk5_0))|~r1_tarski(k1_tops_1(esk3_0,k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,esk5_0)))),k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_143, c_0_144])).
% 44.27/44.51  cnf(c_0_151, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_145, c_0_35])).
% 44.27/44.51  cnf(c_0_152, negated_conjecture, (r1_xboole_0(k7_subset_1(X1,X1,esk5_0),k1_tops_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 44.27/44.51  cnf(c_0_153, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_113, c_0_38])).
% 44.27/44.51  cnf(c_0_154, negated_conjecture, (r1_tarski(k7_subset_1(esk4_0,esk4_0,X1),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_148, c_0_35])).
% 44.27/44.51  cnf(c_0_155, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_149])).
% 44.27/44.51  cnf(c_0_156, plain, (m1_subset_1(X1,X2)|~r1_tarski(k1_zfmisc_1(X3),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_44, c_0_33])).
% 44.27/44.51  cnf(c_0_157, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~r1_xboole_0(k1_tops_1(esk3_0,k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,esk5_0)))),k1_tops_1(esk3_0,esk5_0))|~r1_tarski(k1_tops_1(esk3_0,k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,esk5_0)))),k1_tops_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_38]), c_0_151])])).
% 44.27/44.51  cnf(c_0_158, negated_conjecture, (r1_xboole_0(X1,k1_tops_1(esk3_0,esk5_0))|~r1_tarski(X1,k7_subset_1(X2,X2,esk5_0))), inference(spm,[status(thm)],[c_0_109, c_0_152])).
% 44.27/44.51  cnf(c_0_159, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,k7_subset_1(esk4_0,esk4_0,X1)),k7_subset_1(esk4_0,esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_154]), c_0_115])])).
% 44.27/44.51  cnf(c_0_160, plain, (r1_tarski(X1,k1_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k1_tops_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_42, c_0_155])).
% 44.27/44.51  cnf(c_0_161, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_156, c_0_124])).
% 44.27/44.51  cnf(c_0_162, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~m1_subset_1(esk4_0,k1_zfmisc_1(X2))|~r1_xboole_0(k1_tops_1(esk3_0,k7_subset_1(X2,esk4_0,esk5_0)),k1_tops_1(esk3_0,esk5_0))|~r1_tarski(k1_tops_1(esk3_0,k7_subset_1(X2,esk4_0,esk5_0)),k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_157, c_0_74])).
% 44.27/44.51  cnf(c_0_163, negated_conjecture, (r1_xboole_0(k1_tops_1(esk3_0,k7_subset_1(esk4_0,esk4_0,esk5_0)),k1_tops_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_158, c_0_159])).
% 44.27/44.51  cnf(c_0_164, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~r1_tarski(X1,k1_tops_1(esk3_0,X2))|~r1_tarski(X2,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_97]), c_0_115])]), c_0_161])).
% 44.27/44.51  cnf(c_0_165, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~r1_tarski(k1_tops_1(esk3_0,k7_subset_1(esk4_0,esk4_0,esk5_0)),k1_tops_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_163]), c_0_29])])).
% 44.27/44.51  cnf(c_0_166, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,X1),k1_tops_1(esk3_0,esk4_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_164, c_0_35])).
% 44.27/44.51  cnf(c_0_167, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~r1_tarski(k7_subset_1(esk4_0,esk4_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_165, c_0_166])).
% 44.27/44.51  cnf(c_0_168, plain, (r1_tarski(k7_subset_1(X1,X2,X3),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_87, c_0_74])).
% 44.27/44.51  cnf(c_0_169, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_168]), c_0_29])])).
% 44.27/44.51  cnf(c_0_170, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_97, c_0_169]), ['proof']).
% 44.27/44.51  # SZS output end CNFRefutation
% 44.27/44.51  # Proof object total steps             : 171
% 44.27/44.51  # Proof object clause steps            : 132
% 44.27/44.51  # Proof object formula steps           : 39
% 44.27/44.51  # Proof object conjectures             : 41
% 44.27/44.51  # Proof object clause conjectures      : 38
% 44.27/44.51  # Proof object formula conjectures     : 3
% 44.27/44.51  # Proof object initial clauses used    : 28
% 44.27/44.51  # Proof object initial formulas used   : 19
% 44.27/44.51  # Proof object generating inferences   : 95
% 44.27/44.51  # Proof object simplifying inferences  : 28
% 44.27/44.51  # Training examples: 0 positive, 0 negative
% 44.27/44.51  # Parsed axioms                        : 19
% 44.27/44.51  # Removed by relevancy pruning/SinE    : 0
% 44.27/44.51  # Initial clauses                      : 31
% 44.27/44.51  # Removed in clause preprocessing      : 3
% 44.27/44.51  # Initial clauses in saturation        : 28
% 44.27/44.51  # Processed clauses                    : 71785
% 44.27/44.51  # ...of these trivial                  : 697
% 44.27/44.51  # ...subsumed                          : 45510
% 44.27/44.51  # ...remaining for further processing  : 25578
% 44.27/44.51  # Other redundant clauses eliminated   : 2
% 44.27/44.51  # Clauses deleted for lack of memory   : 50691
% 44.27/44.51  # Backward-subsumed                    : 769
% 44.27/44.51  # Backward-rewritten                   : 47
% 44.27/44.51  # Generated clauses                    : 3063272
% 44.27/44.51  # ...of the previous two non-trivial   : 3004977
% 44.27/44.51  # Contextual simplify-reflections      : 175
% 44.27/44.51  # Paramodulations                      : 3063134
% 44.27/44.51  # Factorizations                       : 130
% 44.27/44.51  # Equation resolutions                 : 2
% 44.27/44.51  # Propositional unsat checks           : 5
% 44.27/44.51  #    Propositional check models        : 0
% 44.27/44.51  #    Propositional check unsatisfiable : 0
% 44.27/44.51  #    Propositional clauses             : 0
% 44.27/44.51  #    Propositional clauses after purity: 0
% 44.27/44.51  #    Propositional unsat core size     : 0
% 44.27/44.51  #    Propositional preprocessing time  : 0.000
% 44.27/44.51  #    Propositional encoding time       : 5.181
% 44.27/44.51  #    Propositional solver time         : 1.437
% 44.27/44.51  #    Success case prop preproc time    : 0.000
% 44.27/44.51  #    Success case prop encoding time   : 0.000
% 44.27/44.51  #    Success case prop solver time     : 0.000
% 44.27/44.51  # Current number of processed clauses  : 24726
% 44.27/44.51  #    Positive orientable unit clauses  : 714
% 44.27/44.51  #    Positive unorientable unit clauses: 0
% 44.27/44.51  #    Negative unit clauses             : 11
% 44.27/44.51  #    Non-unit-clauses                  : 24001
% 44.27/44.51  # Current number of unprocessed clauses: 1782732
% 44.27/44.51  # ...number of literals in the above   : 7123799
% 44.27/44.51  # Current number of archived formulas  : 0
% 44.27/44.51  # Current number of archived clauses   : 853
% 44.27/44.51  # Clause-clause subsumption calls (NU) : 51864664
% 44.27/44.51  # Rec. Clause-clause subsumption calls : 40627734
% 44.27/44.51  # Non-unit clause-clause subsumptions  : 44398
% 44.27/44.51  # Unit Clause-clause subsumption calls : 1805760
% 44.27/44.51  # Rewrite failures with RHS unbound    : 0
% 44.27/44.51  # BW rewrite match attempts            : 5615
% 44.27/44.51  # BW rewrite match successes           : 32
% 44.27/44.51  # Condensation attempts                : 0
% 44.27/44.51  # Condensation successes               : 0
% 44.27/44.51  # Termbank termtop insertions          : 120795952
% 44.44/44.60  
% 44.44/44.60  # -------------------------------------------------
% 44.44/44.60  # User time                : 43.166 s
% 44.44/44.60  # System time              : 1.082 s
% 44.44/44.60  # Total time               : 44.247 s
% 44.44/44.60  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
