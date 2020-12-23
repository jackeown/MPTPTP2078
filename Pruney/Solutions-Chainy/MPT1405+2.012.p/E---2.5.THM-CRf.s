%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:47 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 142 expanded)
%              Number of clauses        :   39 (  63 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  199 ( 445 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t72_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t43_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k1_tops_1(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(t35_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => m2_connsp_2(k2_struct_0(X1),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(d2_connsp_2,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m2_connsp_2(X3,X1,X2)
              <=> r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t80_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(t68_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_16,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r2_hidden(esk3_2(X15,X16),X15)
        | r1_xboole_0(X15,X16) )
      & ( r2_hidden(esk3_2(X15,X16),X16)
        | r1_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_17,plain,(
    ! [X22] : r1_xboole_0(X22,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r2_hidden(esk2_2(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

fof(c_0_26,plain,(
    ! [X24,X25,X26,X27] :
      ( k2_xboole_0(X24,X25) != k2_xboole_0(X26,X27)
      | ~ r1_xboole_0(X26,X24)
      | ~ r1_xboole_0(X27,X25)
      | X26 = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_xboole_1])])).

fof(c_0_27,plain,(
    ! [X21] : k2_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_30,plain,(
    ! [X38] :
      ( ~ l1_struct_0(X38)
      | k2_struct_0(X38) = u1_struct_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_31,plain,(
    ! [X39] :
      ( ~ l1_pre_topc(X39)
      | l1_struct_0(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_32,plain,
    ( X3 = X2
    | k2_xboole_0(X1,X2) != k2_xboole_0(X3,X4)
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_35,plain,(
    ! [X40] :
      ( ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | k1_tops_1(X40,k2_struct_0(X40)) = k2_struct_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_tops_1])])).

cnf(c_0_36,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => m2_connsp_2(k2_struct_0(X1),X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t35_connsp_2])).

fof(c_0_39,plain,(
    ! [X28,X29] :
      ( ~ r1_xboole_0(X28,X29)
      | k4_xboole_0(k2_xboole_0(X28,X29),X29) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])])).

fof(c_0_41,plain,(
    ! [X41,X42,X43] :
      ( ( ~ m2_connsp_2(X43,X41,X42)
        | r1_tarski(X42,k1_tops_1(X41,X43))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( ~ r1_tarski(X42,k1_tops_1(X41,X43))
        | m2_connsp_2(X43,X41,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).

cnf(c_0_42,plain,
    ( k1_tops_1(X1,k2_struct_0(X1)) = k2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_44,plain,(
    ! [X36,X37] :
      ( ( ~ m1_subset_1(X36,k1_zfmisc_1(X37))
        | r1_tarski(X36,X37) )
      & ( ~ r1_tarski(X36,X37)
        | m1_subset_1(X36,k1_zfmisc_1(X37)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ~ m2_connsp_2(k2_struct_0(esk5_0),esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])).

fof(c_0_46,plain,(
    ! [X32] : r1_tarski(k1_tarski(X32),k1_zfmisc_1(X32)) ),
    inference(variable_rename,[status(thm)],[t80_zfmisc_1])).

fof(c_0_47,plain,(
    ! [X30,X31] :
      ( ( k4_xboole_0(k1_tarski(X30),X31) != k1_xboole_0
        | r2_hidden(X30,X31) )
      & ( ~ r2_hidden(X30,X31)
        | k4_xboole_0(k1_tarski(X30),X31) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_zfmisc_1])])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_40,c_0_19])).

cnf(c_0_50,plain,
    ( m2_connsp_2(X3,X2,X1)
    | ~ r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( k1_tops_1(X1,u1_struct_0(X1)) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( ~ m2_connsp_2(k2_struct_0(esk5_0),esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_55,plain,(
    ! [X33,X34] :
      ( ( ~ m1_subset_1(X34,X33)
        | r2_hidden(X34,X33)
        | v1_xboole_0(X33) )
      & ( ~ r2_hidden(X34,X33)
        | m1_subset_1(X34,X33)
        | v1_xboole_0(X33) )
      & ( ~ m1_subset_1(X34,X33)
        | v1_xboole_0(X34)
        | ~ v1_xboole_0(X33) )
      & ( ~ v1_xboole_0(X34)
        | m1_subset_1(X34,X33)
        | ~ v1_xboole_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_56,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_34])])).

cnf(c_0_60,plain,
    ( m2_connsp_2(u1_struct_0(X1),X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_63,negated_conjecture,
    ( ~ m2_connsp_2(u1_struct_0(esk5_0),esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_43]),c_0_54])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_57])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_54])]),c_0_63])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:45:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.21/0.40  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.028 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.21/0.40  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.21/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.40  fof(t72_xboole_1, axiom, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.21/0.40  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.21/0.40  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.21/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.40  fof(t43_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>k1_tops_1(X1,k2_struct_0(X1))=k2_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 0.21/0.40  fof(t35_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>m2_connsp_2(k2_struct_0(X1),X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 0.21/0.40  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.21/0.40  fof(d2_connsp_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,X2)<=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 0.21/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.40  fof(t80_zfmisc_1, axiom, ![X1]:r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 0.21/0.40  fof(t68_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 0.21/0.40  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.21/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.40  fof(c_0_16, plain, ![X15, X16, X18, X19, X20]:(((r2_hidden(esk3_2(X15,X16),X15)|r1_xboole_0(X15,X16))&(r2_hidden(esk3_2(X15,X16),X16)|r1_xboole_0(X15,X16)))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|~r1_xboole_0(X18,X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.21/0.40  fof(c_0_17, plain, ![X22]:r1_xboole_0(X22,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.21/0.40  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_19, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  fof(c_0_20, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.40  cnf(c_0_21, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.40  cnf(c_0_22, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.40  cnf(c_0_23, plain, (r1_tarski(k1_xboole_0,X1)|~r2_hidden(esk2_2(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.40  cnf(c_0_24, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.40  cnf(c_0_25, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.21/0.40  fof(c_0_26, plain, ![X24, X25, X26, X27]:(k2_xboole_0(X24,X25)!=k2_xboole_0(X26,X27)|~r1_xboole_0(X26,X24)|~r1_xboole_0(X27,X25)|X26=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_xboole_1])])).
% 0.21/0.40  fof(c_0_27, plain, ![X21]:k2_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.21/0.40  cnf(c_0_28, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_21])).
% 0.21/0.40  cnf(c_0_29, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  fof(c_0_30, plain, ![X38]:(~l1_struct_0(X38)|k2_struct_0(X38)=u1_struct_0(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.21/0.40  fof(c_0_31, plain, ![X39]:(~l1_pre_topc(X39)|l1_struct_0(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.40  cnf(c_0_32, plain, (X3=X2|k2_xboole_0(X1,X2)!=k2_xboole_0(X3,X4)|~r1_xboole_0(X3,X1)|~r1_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.40  cnf(c_0_33, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.40  cnf(c_0_34, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.40  fof(c_0_35, plain, ![X40]:(~v2_pre_topc(X40)|~l1_pre_topc(X40)|k1_tops_1(X40,k2_struct_0(X40))=k2_struct_0(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_tops_1])])).
% 0.21/0.40  cnf(c_0_36, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  cnf(c_0_37, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.40  fof(c_0_38, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>m2_connsp_2(k2_struct_0(X1),X1,X2)))), inference(assume_negation,[status(cth)],[t35_connsp_2])).
% 0.21/0.40  fof(c_0_39, plain, ![X28, X29]:(~r1_xboole_0(X28,X29)|k4_xboole_0(k2_xboole_0(X28,X29),X29)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.21/0.40  cnf(c_0_40, plain, (k2_xboole_0(X1,X2)=X2|~r1_xboole_0(k2_xboole_0(X1,X2),X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])])).
% 0.21/0.40  fof(c_0_41, plain, ![X41, X42, X43]:((~m2_connsp_2(X43,X41,X42)|r1_tarski(X42,k1_tops_1(X41,X43))|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(~v2_pre_topc(X41)|~l1_pre_topc(X41)))&(~r1_tarski(X42,k1_tops_1(X41,X43))|m2_connsp_2(X43,X41,X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(~v2_pre_topc(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).
% 0.21/0.40  cnf(c_0_42, plain, (k1_tops_1(X1,k2_struct_0(X1))=k2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.40  cnf(c_0_43, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.40  fof(c_0_44, plain, ![X36, X37]:((~m1_subset_1(X36,k1_zfmisc_1(X37))|r1_tarski(X36,X37))&(~r1_tarski(X36,X37)|m1_subset_1(X36,k1_zfmisc_1(X37)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.40  fof(c_0_45, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&~m2_connsp_2(k2_struct_0(esk5_0),esk5_0,esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])).
% 0.21/0.40  fof(c_0_46, plain, ![X32]:r1_tarski(k1_tarski(X32),k1_zfmisc_1(X32)), inference(variable_rename,[status(thm)],[t80_zfmisc_1])).
% 0.21/0.40  fof(c_0_47, plain, ![X30, X31]:((k4_xboole_0(k1_tarski(X30),X31)!=k1_xboole_0|r2_hidden(X30,X31))&(~r2_hidden(X30,X31)|k4_xboole_0(k1_tarski(X30),X31)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_zfmisc_1])])).
% 0.21/0.40  cnf(c_0_48, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.40  cnf(c_0_49, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_40, c_0_19])).
% 0.21/0.40  cnf(c_0_50, plain, (m2_connsp_2(X3,X2,X1)|~r1_tarski(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.40  cnf(c_0_51, plain, (k1_tops_1(X1,u1_struct_0(X1))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.40  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.40  cnf(c_0_53, negated_conjecture, (~m2_connsp_2(k2_struct_0(esk5_0),esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.40  cnf(c_0_54, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.40  fof(c_0_55, plain, ![X33, X34]:(((~m1_subset_1(X34,X33)|r2_hidden(X34,X33)|v1_xboole_0(X33))&(~r2_hidden(X34,X33)|m1_subset_1(X34,X33)|v1_xboole_0(X33)))&((~m1_subset_1(X34,X33)|v1_xboole_0(X34)|~v1_xboole_0(X33))&(~v1_xboole_0(X34)|m1_subset_1(X34,X33)|~v1_xboole_0(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.21/0.40  fof(c_0_56, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.40  cnf(c_0_57, plain, (r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.40  cnf(c_0_58, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.40  cnf(c_0_59, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_34])])).
% 0.21/0.40  cnf(c_0_60, plain, (m2_connsp_2(u1_struct_0(X1),X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.21/0.40  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.40  cnf(c_0_62, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.40  cnf(c_0_63, negated_conjecture, (~m2_connsp_2(u1_struct_0(esk5_0),esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_43]), c_0_54])])).
% 0.21/0.40  cnf(c_0_64, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.40  cnf(c_0_65, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.40  cnf(c_0_66, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_tarski(X2))), inference(spm,[status(thm)],[c_0_24, c_0_57])).
% 0.21/0.40  cnf(c_0_67, plain, (r2_hidden(X1,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.40  cnf(c_0_68, negated_conjecture, (~m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_54])]), c_0_63])).
% 0.21/0.40  cnf(c_0_69, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.40  cnf(c_0_70, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.21/0.40  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 72
% 0.21/0.40  # Proof object clause steps            : 39
% 0.21/0.40  # Proof object formula steps           : 33
% 0.21/0.40  # Proof object conjectures             : 10
% 0.21/0.40  # Proof object clause conjectures      : 7
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 21
% 0.21/0.40  # Proof object initial formulas used   : 16
% 0.21/0.40  # Proof object generating inferences   : 17
% 0.21/0.40  # Proof object simplifying inferences  : 16
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 19
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 35
% 0.21/0.40  # Removed in clause preprocessing      : 0
% 0.21/0.40  # Initial clauses in saturation        : 35
% 0.21/0.40  # Processed clauses                    : 415
% 0.21/0.40  # ...of these trivial                  : 1
% 0.21/0.40  # ...subsumed                          : 220
% 0.21/0.40  # ...remaining for further processing  : 194
% 0.21/0.40  # Other redundant clauses eliminated   : 20
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 5
% 0.21/0.40  # Backward-rewritten                   : 5
% 0.21/0.40  # Generated clauses                    : 1132
% 0.21/0.40  # ...of the previous two non-trivial   : 1037
% 0.21/0.40  # Contextual simplify-reflections      : 6
% 0.21/0.40  # Paramodulations                      : 1111
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 21
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 149
% 0.21/0.40  #    Positive orientable unit clauses  : 23
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 8
% 0.21/0.40  #    Non-unit-clauses                  : 118
% 0.21/0.40  # Current number of unprocessed clauses: 674
% 0.21/0.40  # ...number of literals in the above   : 2928
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 45
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 2821
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 1538
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 166
% 0.21/0.40  # Unit Clause-clause subsumption calls : 147
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 24
% 0.21/0.40  # BW rewrite match successes           : 5
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 14765
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.056 s
% 0.21/0.40  # System time              : 0.003 s
% 0.21/0.40  # Total time               : 0.059 s
% 0.21/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
