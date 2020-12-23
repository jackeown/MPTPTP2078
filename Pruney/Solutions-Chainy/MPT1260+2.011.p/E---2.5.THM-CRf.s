%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:16 EST 2020

% Result     : Theorem 5.57s
% Output     : CNFRefutation 5.57s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 296 expanded)
%              Number of clauses        :   51 ( 134 expanded)
%              Number of leaves         :   14 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  237 ( 861 expanded)
%              Number of equality atoms :   59 ( 295 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_14,plain,(
    ! [X32,X33] : k4_xboole_0(X32,X33) = k5_xboole_0(X32,k3_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,plain,(
    ! [X57,X58] : k1_setfam_1(k2_tarski(X57,X58)) = k3_xboole_0(X57,X58) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X38,X39] : r1_tarski(k4_xboole_0(X38,X39),X38) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X54,X55,X56] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(X54))
      | k7_subset_1(X54,X55,X56) = k4_xboole_0(X55,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X30,X31] :
      ( ( r1_tarski(X30,X31)
        | X30 != X31 )
      & ( r1_tarski(X31,X30)
        | X30 != X31 )
      & ( ~ r1_tarski(X30,X31)
        | ~ r1_tarski(X31,X30)
        | X30 = X31 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_24,plain,(
    ! [X65,X66,X67] :
      ( ~ l1_pre_topc(X65)
      | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))
      | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X65)))
      | ~ v3_pre_topc(X66,X65)
      | ~ r1_tarski(X66,X67)
      | r1_tarski(X66,k1_tops_1(X65,X67)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_25,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_27,plain,(
    ! [X72,X73] :
      ( ~ l1_pre_topc(X72)
      | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))
      | k1_tops_1(X72,X73) = k7_subset_1(u1_struct_0(X72),X73,k2_tops_1(X72,X73)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(k7_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( r2_hidden(X23,X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk3_3(X25,X26,X27),X25)
        | r2_hidden(esk3_3(X25,X26,X27),X26)
        | X27 = k4_xboole_0(X25,X26) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X25)
        | r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk3_3(X25,X26,X27),X26)
        | r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

fof(c_0_35,plain,(
    ! [X63,X64] :
      ( ~ l1_pre_topc(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | k2_tops_1(X63,X64) = k7_subset_1(u1_struct_0(X63),k2_pre_topc(X63,X64),k1_tops_1(X63,X64)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_36,plain,
    ( k1_tops_1(X1,X2) = X3
    | ~ v3_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v3_pre_topc(esk5_0,esk4_0)
      | k2_tops_1(esk4_0,esk5_0) != k7_subset_1(u1_struct_0(esk4_0),k2_pre_topc(esk4_0,esk5_0),esk5_0) )
    & ( v3_pre_topc(esk5_0,esk4_0)
      | k2_tops_1(esk4_0,esk5_0) = k7_subset_1(u1_struct_0(esk4_0),k2_pre_topc(esk4_0,esk5_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

cnf(c_0_41,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( ~ v3_pre_topc(esk5_0,esk4_0)
    | k2_tops_1(esk4_0,esk5_0) != k7_subset_1(u1_struct_0(esk4_0),k2_pre_topc(esk4_0,esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) = k2_tops_1(X1,X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_50,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_43,c_0_21])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk4_0)
    | k2_tops_1(esk4_0,esk5_0) = k7_subset_1(u1_struct_0(esk4_0),k2_pre_topc(esk4_0,esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( ~ v3_pre_topc(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])])).

fof(c_0_54,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(X49))
      | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
      | m1_subset_1(k4_subset_1(X49,X50,X51),k1_zfmisc_1(X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

fof(c_0_55,plain,(
    ! [X70,X71] :
      ( ~ l1_pre_topc(X70)
      | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70)))
      | k2_pre_topc(X70,X71) = k4_subset_1(u1_struct_0(X70),X71,k2_tops_1(X70,X71)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_56,plain,(
    ! [X59,X60] :
      ( ~ l1_pre_topc(X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))
      | m1_subset_1(k2_tops_1(X59,X60),k1_zfmisc_1(u1_struct_0(X59))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_57,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_49,c_0_21])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1
    | r2_hidden(esk3_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k7_subset_1(X2,X1,X4))
    | ~ r2_hidden(X3,X4) ),
    inference(spm,[status(thm)],[c_0_51,c_0_26])).

cnf(c_0_60,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk4_0),k2_pre_topc(esk4_0,esk5_0),esk5_0) = k2_tops_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1
    | r2_hidden(esk3_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,k2_tops_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_67,plain,
    ( k7_subset_1(X1,X2,X3) = X2
    | r2_hidden(esk3_3(X2,X3,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_64])).

cnf(c_0_68,plain,
    ( k7_subset_1(X1,X2,X3) = X2
    | r2_hidden(esk3_3(X2,X3,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_58])).

cnf(c_0_69,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(X1,k2_tops_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_47]),c_0_48])])).

cnf(c_0_71,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk4_0),esk5_0,X1) = esk5_0
    | r2_hidden(esk3_3(esk5_0,X1,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_48])).

cnf(c_0_72,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk4_0),esk5_0,X1) = esk5_0
    | r2_hidden(esk3_3(esk5_0,X1,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_48])).

fof(c_0_73,plain,(
    ! [X61,X62] :
      ( ~ v2_pre_topc(X61)
      | ~ l1_pre_topc(X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))
      | v3_pre_topc(k1_tops_1(X61,X62),X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_74,plain,
    ( k7_subset_1(X1,X2,k2_tops_1(X3,X2)) = k1_tops_1(X3,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk4_0),esk5_0,k2_tops_1(esk4_0,esk5_0)) = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_76,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( k1_tops_1(esk4_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_47]),c_0_48])])).

cnf(c_0_78,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_47]),c_0_48])]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:45:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 5.57/5.83  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 5.57/5.83  # and selection function SelectMaxLComplexAvoidPosPred.
% 5.57/5.83  #
% 5.57/5.83  # Preprocessing time       : 0.029 s
% 5.57/5.83  
% 5.57/5.83  # Proof found!
% 5.57/5.83  # SZS status Theorem
% 5.57/5.83  # SZS output start CNFRefutation
% 5.57/5.83  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.57/5.83  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.57/5.83  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.57/5.83  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.57/5.83  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.57/5.83  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 5.57/5.83  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 5.57/5.83  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.57/5.83  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 5.57/5.83  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.57/5.83  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.57/5.83  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.57/5.83  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.57/5.83  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.57/5.83  fof(c_0_14, plain, ![X32, X33]:k4_xboole_0(X32,X33)=k5_xboole_0(X32,k3_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 5.57/5.83  fof(c_0_15, plain, ![X57, X58]:k1_setfam_1(k2_tarski(X57,X58))=k3_xboole_0(X57,X58), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 5.57/5.83  fof(c_0_16, plain, ![X38, X39]:r1_tarski(k4_xboole_0(X38,X39),X38), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 5.57/5.83  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.57/5.83  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.57/5.83  fof(c_0_19, plain, ![X54, X55, X56]:(~m1_subset_1(X55,k1_zfmisc_1(X54))|k7_subset_1(X54,X55,X56)=k4_xboole_0(X55,X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 5.57/5.83  cnf(c_0_20, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.57/5.83  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 5.57/5.83  cnf(c_0_22, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.57/5.83  fof(c_0_23, plain, ![X30, X31]:(((r1_tarski(X30,X31)|X30!=X31)&(r1_tarski(X31,X30)|X30!=X31))&(~r1_tarski(X30,X31)|~r1_tarski(X31,X30)|X30=X31)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 5.57/5.83  fof(c_0_24, plain, ![X65, X66, X67]:(~l1_pre_topc(X65)|(~m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))|(~m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X65)))|(~v3_pre_topc(X66,X65)|~r1_tarski(X66,X67)|r1_tarski(X66,k1_tops_1(X65,X67)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 5.57/5.83  cnf(c_0_25, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 5.57/5.83  cnf(c_0_26, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 5.57/5.83  fof(c_0_27, plain, ![X72, X73]:(~l1_pre_topc(X72)|(~m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))|k1_tops_1(X72,X73)=k7_subset_1(u1_struct_0(X72),X73,k2_tops_1(X72,X73)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 5.57/5.83  cnf(c_0_28, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.57/5.83  cnf(c_0_29, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.57/5.83  cnf(c_0_30, plain, (r1_tarski(k7_subset_1(X1,X2,X3),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 5.57/5.83  cnf(c_0_31, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 5.57/5.83  cnf(c_0_32, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.57/5.83  fof(c_0_33, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:((((r2_hidden(X23,X20)|~r2_hidden(X23,X22)|X22!=k4_xboole_0(X20,X21))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|X22!=k4_xboole_0(X20,X21)))&(~r2_hidden(X24,X20)|r2_hidden(X24,X21)|r2_hidden(X24,X22)|X22!=k4_xboole_0(X20,X21)))&((~r2_hidden(esk3_3(X25,X26,X27),X27)|(~r2_hidden(esk3_3(X25,X26,X27),X25)|r2_hidden(esk3_3(X25,X26,X27),X26))|X27=k4_xboole_0(X25,X26))&((r2_hidden(esk3_3(X25,X26,X27),X25)|r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k4_xboole_0(X25,X26))&(~r2_hidden(esk3_3(X25,X26,X27),X26)|r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k4_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 5.57/5.83  fof(c_0_34, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 5.57/5.83  fof(c_0_35, plain, ![X63, X64]:(~l1_pre_topc(X63)|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))|k2_tops_1(X63,X64)=k7_subset_1(u1_struct_0(X63),k2_pre_topc(X63,X64),k1_tops_1(X63,X64)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 5.57/5.83  cnf(c_0_36, plain, (k1_tops_1(X1,X2)=X3|~v3_pre_topc(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 5.57/5.83  cnf(c_0_37, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 5.57/5.83  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 5.57/5.83  cnf(c_0_39, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 5.57/5.83  fof(c_0_40, negated_conjecture, ((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((~v3_pre_topc(esk5_0,esk4_0)|k2_tops_1(esk4_0,esk5_0)!=k7_subset_1(u1_struct_0(esk4_0),k2_pre_topc(esk4_0,esk5_0),esk5_0))&(v3_pre_topc(esk5_0,esk4_0)|k2_tops_1(esk4_0,esk5_0)=k7_subset_1(u1_struct_0(esk4_0),k2_pre_topc(esk4_0,esk5_0),esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).
% 5.57/5.83  cnf(c_0_41, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 5.57/5.83  cnf(c_0_42, plain, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 5.57/5.83  cnf(c_0_43, plain, (r2_hidden(esk3_3(X1,X2,X3),X1)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 5.57/5.83  cnf(c_0_44, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_21])).
% 5.57/5.83  cnf(c_0_45, negated_conjecture, (~v3_pre_topc(esk5_0,esk4_0)|k2_tops_1(esk4_0,esk5_0)!=k7_subset_1(u1_struct_0(esk4_0),k2_pre_topc(esk4_0,esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.57/5.83  cnf(c_0_46, plain, (k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)=k2_tops_1(X1,X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 5.57/5.83  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.57/5.83  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.57/5.83  cnf(c_0_49, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk3_3(X1,X2,X3),X3)|~r2_hidden(esk3_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 5.57/5.83  cnf(c_0_50, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk3_3(X1,X2,X3),X3)|r2_hidden(esk3_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_43, c_0_21])).
% 5.57/5.83  cnf(c_0_51, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_44])).
% 5.57/5.83  cnf(c_0_52, negated_conjecture, (v3_pre_topc(esk5_0,esk4_0)|k2_tops_1(esk4_0,esk5_0)=k7_subset_1(u1_struct_0(esk4_0),k2_pre_topc(esk4_0,esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.57/5.83  cnf(c_0_53, negated_conjecture, (~v3_pre_topc(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])])).
% 5.57/5.83  fof(c_0_54, plain, ![X49, X50, X51]:(~m1_subset_1(X50,k1_zfmisc_1(X49))|~m1_subset_1(X51,k1_zfmisc_1(X49))|m1_subset_1(k4_subset_1(X49,X50,X51),k1_zfmisc_1(X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 5.57/5.83  fof(c_0_55, plain, ![X70, X71]:(~l1_pre_topc(X70)|(~m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70)))|k2_pre_topc(X70,X71)=k4_subset_1(u1_struct_0(X70),X71,k2_tops_1(X70,X71)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 5.57/5.83  fof(c_0_56, plain, ![X59, X60]:(~l1_pre_topc(X59)|~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))|m1_subset_1(k2_tops_1(X59,X60),k1_zfmisc_1(u1_struct_0(X59)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 5.57/5.83  cnf(c_0_57, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(esk3_3(X1,X2,X3),X3)|~r2_hidden(esk3_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_49, c_0_21])).
% 5.57/5.83  cnf(c_0_58, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1|r2_hidden(esk3_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_50])).
% 5.57/5.83  cnf(c_0_59, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k7_subset_1(X2,X1,X4))|~r2_hidden(X3,X4)), inference(spm,[status(thm)],[c_0_51, c_0_26])).
% 5.57/5.83  cnf(c_0_60, negated_conjecture, (k7_subset_1(u1_struct_0(esk4_0),k2_pre_topc(esk4_0,esk5_0),esk5_0)=k2_tops_1(esk4_0,esk5_0)), inference(sr,[status(thm)],[c_0_52, c_0_53])).
% 5.57/5.83  cnf(c_0_61, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 5.57/5.83  cnf(c_0_62, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 5.57/5.83  cnf(c_0_63, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 5.57/5.83  cnf(c_0_64, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1|r2_hidden(esk3_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_58])).
% 5.57/5.83  cnf(c_0_65, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,k2_tops_1(esk4_0,esk5_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 5.57/5.83  cnf(c_0_66, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 5.57/5.83  cnf(c_0_67, plain, (k7_subset_1(X1,X2,X3)=X2|r2_hidden(esk3_3(X2,X3,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_64])).
% 5.57/5.83  cnf(c_0_68, plain, (k7_subset_1(X1,X2,X3)=X2|r2_hidden(esk3_3(X2,X3,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_58])).
% 5.57/5.83  cnf(c_0_69, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_26, c_0_26])).
% 5.57/5.83  cnf(c_0_70, negated_conjecture, (~r2_hidden(X1,k2_tops_1(esk4_0,esk5_0))|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_47]), c_0_48])])).
% 5.57/5.83  cnf(c_0_71, negated_conjecture, (k7_subset_1(u1_struct_0(esk4_0),esk5_0,X1)=esk5_0|r2_hidden(esk3_3(esk5_0,X1,esk5_0),X1)), inference(spm,[status(thm)],[c_0_67, c_0_48])).
% 5.57/5.83  cnf(c_0_72, negated_conjecture, (k7_subset_1(u1_struct_0(esk4_0),esk5_0,X1)=esk5_0|r2_hidden(esk3_3(esk5_0,X1,esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_48])).
% 5.57/5.83  fof(c_0_73, plain, ![X61, X62]:(~v2_pre_topc(X61)|~l1_pre_topc(X61)|~m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))|v3_pre_topc(k1_tops_1(X61,X62),X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 5.57/5.83  cnf(c_0_74, plain, (k7_subset_1(X1,X2,k2_tops_1(X3,X2))=k1_tops_1(X3,X2)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_69])).
% 5.57/5.83  cnf(c_0_75, negated_conjecture, (k7_subset_1(u1_struct_0(esk4_0),esk5_0,k2_tops_1(esk4_0,esk5_0))=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 5.57/5.83  cnf(c_0_76, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 5.57/5.83  cnf(c_0_77, negated_conjecture, (k1_tops_1(esk4_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_47]), c_0_48])])).
% 5.57/5.83  cnf(c_0_78, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.57/5.83  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_47]), c_0_48])]), c_0_53]), ['proof']).
% 5.57/5.83  # SZS output end CNFRefutation
% 5.57/5.83  # Proof object total steps             : 80
% 5.57/5.83  # Proof object clause steps            : 51
% 5.57/5.83  # Proof object formula steps           : 29
% 5.57/5.83  # Proof object conjectures             : 17
% 5.57/5.83  # Proof object clause conjectures      : 14
% 5.57/5.83  # Proof object formula conjectures     : 3
% 5.57/5.83  # Proof object initial clauses used    : 21
% 5.57/5.83  # Proof object initial formulas used   : 14
% 5.57/5.83  # Proof object generating inferences   : 21
% 5.57/5.83  # Proof object simplifying inferences  : 28
% 5.57/5.83  # Training examples: 0 positive, 0 negative
% 5.57/5.83  # Parsed axioms                        : 26
% 5.57/5.83  # Removed by relevancy pruning/SinE    : 0
% 5.57/5.83  # Initial clauses                      : 44
% 5.57/5.83  # Removed in clause preprocessing      : 3
% 5.57/5.83  # Initial clauses in saturation        : 41
% 5.57/5.83  # Processed clauses                    : 10668
% 5.57/5.83  # ...of these trivial                  : 158
% 5.57/5.83  # ...subsumed                          : 8452
% 5.57/5.83  # ...remaining for further processing  : 2058
% 5.57/5.83  # Other redundant clauses eliminated   : 35
% 5.57/5.83  # Clauses deleted for lack of memory   : 0
% 5.57/5.83  # Backward-subsumed                    : 263
% 5.57/5.83  # Backward-rewritten                   : 101
% 5.57/5.83  # Generated clauses                    : 437305
% 5.57/5.83  # ...of the previous two non-trivial   : 406582
% 5.57/5.83  # Contextual simplify-reflections      : 84
% 5.57/5.83  # Paramodulations                      : 436875
% 5.57/5.83  # Factorizations                       : 394
% 5.57/5.83  # Equation resolutions                 : 35
% 5.57/5.83  # Propositional unsat checks           : 0
% 5.57/5.83  #    Propositional check models        : 0
% 5.57/5.83  #    Propositional check unsatisfiable : 0
% 5.57/5.83  #    Propositional clauses             : 0
% 5.57/5.83  #    Propositional clauses after purity: 0
% 5.57/5.83  #    Propositional unsat core size     : 0
% 5.57/5.83  #    Propositional preprocessing time  : 0.000
% 5.57/5.83  #    Propositional encoding time       : 0.000
% 5.57/5.83  #    Propositional solver time         : 0.000
% 5.57/5.83  #    Success case prop preproc time    : 0.000
% 5.57/5.83  #    Success case prop encoding time   : 0.000
% 5.57/5.83  #    Success case prop solver time     : 0.000
% 5.57/5.83  # Current number of processed clauses  : 1685
% 5.57/5.83  #    Positive orientable unit clauses  : 100
% 5.57/5.83  #    Positive unorientable unit clauses: 1
% 5.57/5.83  #    Negative unit clauses             : 2
% 5.57/5.83  #    Non-unit-clauses                  : 1582
% 5.57/5.83  # Current number of unprocessed clauses: 395319
% 5.57/5.83  # ...number of literals in the above   : 1880537
% 5.57/5.83  # Current number of archived formulas  : 0
% 5.57/5.83  # Current number of archived clauses   : 368
% 5.57/5.83  # Clause-clause subsumption calls (NU) : 309186
% 5.57/5.83  # Rec. Clause-clause subsumption calls : 172719
% 5.57/5.83  # Non-unit clause-clause subsumptions  : 7711
% 5.57/5.83  # Unit Clause-clause subsumption calls : 3134
% 5.57/5.83  # Rewrite failures with RHS unbound    : 0
% 5.57/5.83  # BW rewrite match attempts            : 1057
% 5.57/5.83  # BW rewrite match successes           : 29
% 5.57/5.83  # Condensation attempts                : 0
% 5.57/5.83  # Condensation successes               : 0
% 5.57/5.83  # Termbank termtop insertions          : 10610720
% 5.67/5.85  
% 5.67/5.85  # -------------------------------------------------
% 5.67/5.85  # User time                : 5.327 s
% 5.67/5.85  # System time              : 0.174 s
% 5.67/5.85  # Total time               : 5.501 s
% 5.67/5.85  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
