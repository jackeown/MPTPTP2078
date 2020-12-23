%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:03 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 653 expanded)
%              Number of clauses        :   69 ( 258 expanded)
%              Number of leaves         :   17 ( 161 expanded)
%              Depth                    :   20
%              Number of atoms          :  292 (3388 expanded)
%              Number of equality atoms :   62 ( 496 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t86_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X1) )
                 => X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

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

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(c_0_17,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X21,X22] : k1_setfam_1(k2_tarski(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | ~ r1_tarski(X26,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_20,plain,(
    ! [X27,X29,X30,X31] :
      ( ( r2_hidden(esk1_1(X27),X27)
        | X27 = k1_xboole_0 )
      & ( ~ r2_hidden(X29,X27)
        | esk1_1(X27) != k3_mcart_1(X29,X30,X31)
        | X27 = k1_xboole_0 )
      & ( ~ r2_hidden(X30,X27)
        | esk1_1(X27) != k3_mcart_1(X29,X30,X31)
        | X27 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

fof(c_0_21,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | r1_tarski(k4_xboole_0(X8,X10),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_28,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,esk1_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3))),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_31,plain,(
    ! [X16] : r1_tarski(k1_xboole_0,X16) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,esk1_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_35,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k3_xboole_0(X14,X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_23]),c_0_27]),c_0_27])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_38,plain,(
    ! [X19,X20] : k2_tarski(X19,X20) = k2_tarski(X20,X19) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_37])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_42,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_43,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tops_1(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X1) )
                   => X3 = k1_xboole_0 ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_tops_1])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_23])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_47,plain,(
    ! [X36,X37] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | r1_tarski(k1_tops_1(X36,X37),X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_51,negated_conjecture,(
    ! [X50] :
      ( v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v2_tops_1(esk4_0,esk3_0) )
      & ( r1_tarski(esk5_0,esk4_0)
        | ~ v2_tops_1(esk4_0,esk3_0) )
      & ( v3_pre_topc(esk5_0,esk3_0)
        | ~ v2_tops_1(esk4_0,esk3_0) )
      & ( esk5_0 != k1_xboole_0
        | ~ v2_tops_1(esk4_0,esk3_0) )
      & ( v2_tops_1(esk4_0,esk3_0)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ r1_tarski(X50,esk4_0)
        | ~ v3_pre_topc(X50,esk3_0)
        | X50 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])])])).

fof(c_0_52,plain,(
    ! [X32,X33] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | v3_pre_topc(k1_tops_1(X32,X33),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_53,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_34])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_58,plain,(
    ! [X41,X42,X43,X44] :
      ( ( ~ v3_pre_topc(X44,X42)
        | k1_tops_1(X42,X44) = X44
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_pre_topc(X42)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( k1_tops_1(X41,X43) != X43
        | v3_pre_topc(X43,X41)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_pre_topc(X42)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_59,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( k1_tops_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( v3_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_55])])).

cnf(c_0_66,negated_conjecture,
    ( v2_tops_1(esk4_0,esk3_0)
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_61])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,esk1_1(k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_36])).

cnf(c_0_69,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_41])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_34])).

fof(c_0_71,plain,(
    ! [X38,X39,X40] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
      | ~ r1_tarski(X39,X40)
      | r1_tarski(k1_tops_1(X38,X39),k1_tops_1(X38,X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_72,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_57]),c_0_63]),c_0_64])])).

cnf(c_0_73,negated_conjecture,
    ( v3_pre_topc(k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_64]),c_0_63])])).

cnf(c_0_74,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_tops_1(esk4_0,esk3_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X2,esk1_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_50])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k1_tops_1(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_63]),c_0_55])])).

cnf(c_0_79,negated_conjecture,
    ( k1_tops_1(esk3_0,X1) = k1_xboole_0
    | v2_tops_1(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk3_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_59]),c_0_63]),c_0_64])])).

fof(c_0_80,plain,(
    ! [X45,X46] :
      ( ( ~ v2_tops_1(X46,X45)
        | k1_tops_1(X45,X46) = k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) )
      & ( k1_tops_1(X45,X46) != k1_xboole_0
        | v2_tops_1(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

cnf(c_0_81,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk3_0)
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_83,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,X1),k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_63]),c_0_55])])).

cnf(c_0_85,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = k1_xboole_0
    | v2_tops_1(esk4_0,esk3_0)
    | ~ r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_57])).

cnf(c_0_86,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k1_tops_1(esk3_0,esk5_0) = esk5_0
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_81]),c_0_63])]),c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_89,plain,
    ( v2_tops_1(X2,X1)
    | k1_tops_1(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( k1_tops_1(esk3_0,X1) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_55])])).

cnf(c_0_91,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = k1_xboole_0
    | v2_tops_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_54]),c_0_63]),c_0_57])])).

cnf(c_0_92,negated_conjecture,
    ( ~ v2_tops_1(esk5_0,esk3_0)
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_63])]),c_0_82]),c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( v2_tops_1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_63])])).

cnf(c_0_94,negated_conjecture,
    ( v2_tops_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_91]),c_0_63]),c_0_57])])).

cnf(c_0_95,negated_conjecture,
    ( ~ v2_tops_1(esk4_0,esk3_0)
    | ~ r1_tarski(esk5_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_82])).

cnf(c_0_96,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_xboole_0)
    | ~ v2_tops_1(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_77,c_0_86])).

cnf(c_0_97,negated_conjecture,
    ( k1_tops_1(esk3_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_94])])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_94])])).

cnf(c_0_99,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_94])])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_101,negated_conjecture,
    ( ~ v2_tops_1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_63]),c_0_98])]),c_0_99])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_94])])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_94]),c_0_57]),c_0_102])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:27:56 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.15/0.43  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.15/0.43  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.15/0.43  #
% 0.15/0.43  # Preprocessing time       : 0.029 s
% 0.15/0.43  
% 0.15/0.43  # Proof found!
% 0.15/0.43  # SZS status Theorem
% 0.15/0.43  # SZS output start CNFRefutation
% 0.15/0.43  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.15/0.43  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.15/0.43  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.15/0.43  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.15/0.43  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 0.15/0.43  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.15/0.43  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.15/0.43  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.15/0.43  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.15/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.15/0.43  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.15/0.43  fof(t86_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 0.15/0.43  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.15/0.43  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.15/0.43  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 0.15/0.43  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.15/0.43  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 0.15/0.43  fof(c_0_17, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.15/0.43  fof(c_0_18, plain, ![X21, X22]:k1_setfam_1(k2_tarski(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.15/0.43  fof(c_0_19, plain, ![X25, X26]:(~r2_hidden(X25,X26)|~r1_tarski(X26,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.15/0.43  fof(c_0_20, plain, ![X27, X29, X30, X31]:((r2_hidden(esk1_1(X27),X27)|X27=k1_xboole_0)&((~r2_hidden(X29,X27)|esk1_1(X27)!=k3_mcart_1(X29,X30,X31)|X27=k1_xboole_0)&(~r2_hidden(X30,X27)|esk1_1(X27)!=k3_mcart_1(X29,X30,X31)|X27=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.15/0.43  fof(c_0_21, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|r1_tarski(k4_xboole_0(X8,X10),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 0.15/0.43  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.43  cnf(c_0_23, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.43  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.43  cnf(c_0_25, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.43  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.43  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.15/0.43  fof(c_0_28, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.15/0.43  cnf(c_0_29, plain, (X1=k1_xboole_0|~r1_tarski(X1,esk1_1(X1))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.15/0.43  cnf(c_0_30, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3))),X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.15/0.43  fof(c_0_31, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.15/0.43  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.15/0.43  cnf(c_0_33, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,esk1_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.15/0.43  cnf(c_0_34, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.15/0.43  fof(c_0_35, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k3_xboole_0(X14,X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.15/0.43  cnf(c_0_36, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_23]), c_0_27]), c_0_27])).
% 0.15/0.43  cnf(c_0_37, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.15/0.43  fof(c_0_38, plain, ![X19, X20]:k2_tarski(X19,X20)=k2_tarski(X20,X19), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.15/0.43  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.15/0.43  cnf(c_0_40, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_37])).
% 0.15/0.43  cnf(c_0_41, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.15/0.43  fof(c_0_42, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.15/0.43  fof(c_0_43, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.15/0.43  fof(c_0_44, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t86_tops_1])).
% 0.15/0.43  cnf(c_0_45, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_23])).
% 0.15/0.43  cnf(c_0_46, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.15/0.43  fof(c_0_47, plain, ![X36, X37]:(~l1_pre_topc(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|r1_tarski(k1_tops_1(X36,X37),X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.15/0.43  cnf(c_0_48, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.15/0.43  cnf(c_0_49, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.15/0.43  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.15/0.43  fof(c_0_51, negated_conjecture, ![X50]:((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(((m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v2_tops_1(esk4_0,esk3_0))&(((r1_tarski(esk5_0,esk4_0)|~v2_tops_1(esk4_0,esk3_0))&(v3_pre_topc(esk5_0,esk3_0)|~v2_tops_1(esk4_0,esk3_0)))&(esk5_0!=k1_xboole_0|~v2_tops_1(esk4_0,esk3_0))))&(v2_tops_1(esk4_0,esk3_0)|(~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(esk3_0)))|(~r1_tarski(X50,esk4_0)|~v3_pre_topc(X50,esk3_0)|X50=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])])])).
% 0.15/0.43  fof(c_0_52, plain, ![X32, X33]:(~v2_pre_topc(X32)|~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|v3_pre_topc(k1_tops_1(X32,X33),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.15/0.43  cnf(c_0_53, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.15/0.43  cnf(c_0_54, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.15/0.43  cnf(c_0_55, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_34])).
% 0.15/0.43  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.15/0.43  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.15/0.43  fof(c_0_58, plain, ![X41, X42, X43, X44]:((~v3_pre_topc(X44,X42)|k1_tops_1(X42,X44)=X44|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~l1_pre_topc(X42)|(~v2_pre_topc(X41)|~l1_pre_topc(X41)))&(k1_tops_1(X41,X43)!=X43|v3_pre_topc(X43,X41)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~l1_pre_topc(X42)|(~v2_pre_topc(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.15/0.43  cnf(c_0_59, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.15/0.43  cnf(c_0_60, plain, (k1_tops_1(X1,k1_xboole_0)=k1_xboole_0|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.15/0.43  cnf(c_0_61, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.15/0.43  cnf(c_0_62, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.15/0.43  cnf(c_0_63, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.15/0.43  cnf(c_0_64, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.15/0.43  cnf(c_0_65, plain, (v3_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_55])])).
% 0.15/0.43  cnf(c_0_66, negated_conjecture, (v2_tops_1(esk4_0,esk3_0)|X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)|~v3_pre_topc(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.15/0.43  cnf(c_0_67, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_61])).
% 0.15/0.43  cnf(c_0_68, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r1_tarski(X1,esk1_1(k1_setfam_1(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_33, c_0_36])).
% 0.15/0.43  cnf(c_0_69, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_41])).
% 0.15/0.43  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_34])).
% 0.15/0.43  fof(c_0_71, plain, ![X38, X39, X40]:(~l1_pre_topc(X38)|(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|(~r1_tarski(X39,X40)|r1_tarski(k1_tops_1(X38,X39),k1_tops_1(X38,X40)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.15/0.43  cnf(c_0_72, negated_conjecture, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_57]), c_0_63]), c_0_64])])).
% 0.15/0.43  cnf(c_0_73, negated_conjecture, (v3_pre_topc(k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_64]), c_0_63])])).
% 0.15/0.43  cnf(c_0_74, negated_conjecture, (X1=k1_xboole_0|v2_tops_1(esk4_0,esk3_0)|~v3_pre_topc(X1,esk3_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.15/0.43  cnf(c_0_75, plain, (X1=k1_xboole_0|~r1_tarski(X2,esk1_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.15/0.43  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_70, c_0_50])).
% 0.15/0.43  cnf(c_0_77, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.15/0.43  cnf(c_0_78, negated_conjecture, (k1_tops_1(esk3_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_63]), c_0_55])])).
% 0.15/0.43  cnf(c_0_79, negated_conjecture, (k1_tops_1(esk3_0,X1)=k1_xboole_0|v2_tops_1(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_59]), c_0_63]), c_0_64])])).
% 0.15/0.43  fof(c_0_80, plain, ![X45, X46]:((~v2_tops_1(X46,X45)|k1_tops_1(X45,X46)=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))&(k1_tops_1(X45,X46)!=k1_xboole_0|v2_tops_1(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.15/0.43  cnf(c_0_81, negated_conjecture, (v3_pre_topc(esk5_0,esk3_0)|~v2_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.15/0.43  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v2_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.15/0.43  cnf(c_0_83, plain, (X1=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.15/0.43  cnf(c_0_84, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,X1),k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_63]), c_0_55])])).
% 0.15/0.43  cnf(c_0_85, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=k1_xboole_0|v2_tops_1(esk4_0,esk3_0)|~r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_79, c_0_57])).
% 0.15/0.43  cnf(c_0_86, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.15/0.43  cnf(c_0_87, negated_conjecture, (k1_tops_1(esk3_0,esk5_0)=esk5_0|~v2_tops_1(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_81]), c_0_63])]), c_0_82])).
% 0.15/0.43  cnf(c_0_88, negated_conjecture, (esk5_0!=k1_xboole_0|~v2_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.15/0.43  cnf(c_0_89, plain, (v2_tops_1(X2,X1)|k1_tops_1(X1,X2)!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.15/0.43  cnf(c_0_90, negated_conjecture, (k1_tops_1(esk3_0,X1)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_55])])).
% 0.15/0.43  cnf(c_0_91, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=k1_xboole_0|v2_tops_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_54]), c_0_63]), c_0_57])])).
% 0.15/0.43  cnf(c_0_92, negated_conjecture, (~v2_tops_1(esk5_0,esk3_0)|~v2_tops_1(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_63])]), c_0_82]), c_0_88])).
% 0.15/0.43  cnf(c_0_93, negated_conjecture, (v2_tops_1(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_63])])).
% 0.15/0.43  cnf(c_0_94, negated_conjecture, (v2_tops_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_91]), c_0_63]), c_0_57])])).
% 0.15/0.43  cnf(c_0_95, negated_conjecture, (~v2_tops_1(esk4_0,esk3_0)|~r1_tarski(esk5_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_82])).
% 0.15/0.43  cnf(c_0_96, plain, (r1_tarski(k1_tops_1(X1,X2),k1_xboole_0)|~v2_tops_1(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_77, c_0_86])).
% 0.15/0.43  cnf(c_0_97, negated_conjecture, (k1_tops_1(esk3_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_94])])).
% 0.15/0.43  cnf(c_0_98, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_94])])).
% 0.15/0.43  cnf(c_0_99, negated_conjecture, (~r1_tarski(esk5_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_94])])).
% 0.15/0.43  cnf(c_0_100, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~v2_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.15/0.43  cnf(c_0_101, negated_conjecture, (~v2_tops_1(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk5_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_63]), c_0_98])]), c_0_99])).
% 0.15/0.43  cnf(c_0_102, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_94])])).
% 0.15/0.43  cnf(c_0_103, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_94]), c_0_57]), c_0_102])]), ['proof']).
% 0.15/0.43  # SZS output end CNFRefutation
% 0.15/0.43  # Proof object total steps             : 104
% 0.15/0.43  # Proof object clause steps            : 69
% 0.15/0.43  # Proof object formula steps           : 35
% 0.15/0.43  # Proof object conjectures             : 33
% 0.15/0.43  # Proof object clause conjectures      : 30
% 0.15/0.43  # Proof object formula conjectures     : 3
% 0.15/0.43  # Proof object initial clauses used    : 26
% 0.15/0.43  # Proof object initial formulas used   : 17
% 0.15/0.43  # Proof object generating inferences   : 35
% 0.15/0.43  # Proof object simplifying inferences  : 58
% 0.15/0.43  # Training examples: 0 positive, 0 negative
% 0.15/0.43  # Parsed axioms                        : 18
% 0.15/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.43  # Initial clauses                      : 31
% 0.15/0.43  # Removed in clause preprocessing      : 2
% 0.15/0.43  # Initial clauses in saturation        : 29
% 0.15/0.43  # Processed clauses                    : 313
% 0.15/0.43  # ...of these trivial                  : 3
% 0.15/0.43  # ...subsumed                          : 130
% 0.15/0.43  # ...remaining for further processing  : 180
% 0.15/0.43  # Other redundant clauses eliminated   : 0
% 0.15/0.43  # Clauses deleted for lack of memory   : 0
% 0.15/0.43  # Backward-subsumed                    : 11
% 0.15/0.43  # Backward-rewritten                   : 20
% 0.15/0.43  # Generated clauses                    : 1318
% 0.15/0.43  # ...of the previous two non-trivial   : 1028
% 0.15/0.43  # Contextual simplify-reflections      : 14
% 0.15/0.43  # Paramodulations                      : 1318
% 0.15/0.43  # Factorizations                       : 0
% 0.15/0.43  # Equation resolutions                 : 0
% 0.15/0.43  # Propositional unsat checks           : 0
% 0.15/0.43  #    Propositional check models        : 0
% 0.15/0.43  #    Propositional check unsatisfiable : 0
% 0.15/0.43  #    Propositional clauses             : 0
% 0.15/0.43  #    Propositional clauses after purity: 0
% 0.15/0.43  #    Propositional unsat core size     : 0
% 0.15/0.43  #    Propositional preprocessing time  : 0.000
% 0.15/0.43  #    Propositional encoding time       : 0.000
% 0.15/0.43  #    Propositional solver time         : 0.000
% 0.15/0.43  #    Success case prop preproc time    : 0.000
% 0.15/0.43  #    Success case prop encoding time   : 0.000
% 0.15/0.43  #    Success case prop solver time     : 0.000
% 0.15/0.43  # Current number of processed clauses  : 149
% 0.15/0.43  #    Positive orientable unit clauses  : 21
% 0.15/0.43  #    Positive unorientable unit clauses: 1
% 0.15/0.43  #    Negative unit clauses             : 5
% 0.15/0.43  #    Non-unit-clauses                  : 122
% 0.15/0.43  # Current number of unprocessed clauses: 734
% 0.15/0.43  # ...number of literals in the above   : 2386
% 0.15/0.43  # Current number of archived formulas  : 0
% 0.15/0.43  # Current number of archived clauses   : 33
% 0.15/0.43  # Clause-clause subsumption calls (NU) : 3604
% 0.15/0.43  # Rec. Clause-clause subsumption calls : 2159
% 0.15/0.43  # Non-unit clause-clause subsumptions  : 133
% 0.15/0.43  # Unit Clause-clause subsumption calls : 100
% 0.15/0.43  # Rewrite failures with RHS unbound    : 0
% 0.15/0.43  # BW rewrite match attempts            : 23
% 0.15/0.43  # BW rewrite match successes           : 6
% 0.15/0.43  # Condensation attempts                : 0
% 0.15/0.43  # Condensation successes               : 0
% 0.15/0.43  # Termbank termtop insertions          : 21527
% 0.15/0.43  
% 0.15/0.43  # -------------------------------------------------
% 0.15/0.43  # User time                : 0.066 s
% 0.15/0.43  # System time              : 0.003 s
% 0.15/0.43  # Total time               : 0.069 s
% 0.15/0.43  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
