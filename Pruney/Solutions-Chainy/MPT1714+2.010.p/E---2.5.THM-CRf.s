%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:58 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 475 expanded)
%              Number of clauses        :   45 ( 189 expanded)
%              Number of leaves         :   11 ( 118 expanded)
%              Depth                    :   19
%              Number of atoms          :  261 (2982 expanded)
%              Number of equality atoms :   17 (  50 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( m1_pre_topc(X2,X3)
                   => ( ( r1_tsep_1(X2,X4)
                        & r1_tsep_1(X4,X2) )
                      | ( ~ r1_tsep_1(X3,X4)
                        & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( m1_pre_topc(X2,X3)
                     => ( ( r1_tsep_1(X2,X4)
                          & r1_tsep_1(X4,X2) )
                        | ( ~ r1_tsep_1(X3,X4)
                          & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_tmap_1])).

fof(c_0_12,plain,(
    ! [X16,X17,X18,X20,X22] :
      ( ( r1_tarski(k2_struct_0(X17),k2_struct_0(X16))
        | ~ m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk1_3(X16,X17,X18),u1_pre_topc(X16))
        | ~ r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( X18 = k9_subset_1(u1_struct_0(X17),esk1_3(X16,X17,X18),k2_struct_0(X17))
        | ~ r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r2_hidden(X20,u1_pre_topc(X16))
        | X18 != k9_subset_1(u1_struct_0(X17),X20,k2_struct_0(X17))
        | r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk2_2(X16,X17),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r1_tarski(k2_struct_0(X17),k2_struct_0(X16))
        | m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( ~ r2_hidden(esk2_2(X16,X17),u1_pre_topc(X17))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r2_hidden(X22,u1_pre_topc(X16))
        | esk2_2(X16,X17) != k9_subset_1(u1_struct_0(X17),X22,k2_struct_0(X17))
        | ~ r1_tarski(k2_struct_0(X17),k2_struct_0(X16))
        | m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk3_2(X16,X17),k1_zfmisc_1(u1_struct_0(X16)))
        | r2_hidden(esk2_2(X16,X17),u1_pre_topc(X17))
        | ~ r1_tarski(k2_struct_0(X17),k2_struct_0(X16))
        | m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk3_2(X16,X17),u1_pre_topc(X16))
        | r2_hidden(esk2_2(X16,X17),u1_pre_topc(X17))
        | ~ r1_tarski(k2_struct_0(X17),k2_struct_0(X16))
        | m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( esk2_2(X16,X17) = k9_subset_1(u1_struct_0(X17),esk3_2(X16,X17),k2_struct_0(X17))
        | r2_hidden(esk2_2(X16,X17),u1_pre_topc(X17))
        | ~ r1_tarski(k2_struct_0(X17),k2_struct_0(X16))
        | m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_13,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_pre_topc(X26,X25)
      | l1_pre_topc(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk4_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk4_0)
    & ~ v2_struct_0(esk7_0)
    & m1_pre_topc(esk7_0,esk4_0)
    & m1_pre_topc(esk5_0,esk6_0)
    & ( ~ r1_tsep_1(esk5_0,esk7_0)
      | ~ r1_tsep_1(esk7_0,esk5_0) )
    & ( r1_tsep_1(esk6_0,esk7_0)
      | r1_tsep_1(esk7_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_15,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X36,X37] :
      ( ~ l1_struct_0(X36)
      | ~ l1_struct_0(X37)
      | ~ r1_tsep_1(X36,X37)
      | r1_tsep_1(X37,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

fof(c_0_20,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X14,X13)
      | r1_tarski(k2_xboole_0(X12,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_24,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_25,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r1_tsep_1(esk6_0,esk7_0)
    | r1_tsep_1(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_27,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | l1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0)
    | ~ l1_struct_0(esk7_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_28]),c_0_18])])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,k2_struct_0(esk5_0)),k2_struct_0(esk6_0))
    | ~ r1_tarski(X1,k2_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X10,X11] : r1_tarski(X10,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_38,plain,(
    ! [X15] :
      ( ~ l1_struct_0(X15)
      | k2_struct_0(X15) = u1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_39,plain,(
    ! [X31,X32] :
      ( ( ~ r1_tsep_1(X31,X32)
        | r1_xboole_0(u1_struct_0(X31),u1_struct_0(X32))
        | ~ l1_struct_0(X32)
        | ~ l1_struct_0(X31) )
      & ( ~ r1_xboole_0(u1_struct_0(X31),u1_struct_0(X32))
        | r1_tsep_1(X31,X32)
        | ~ l1_struct_0(X32)
        | ~ l1_struct_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k2_struct_0(esk6_0),k2_struct_0(esk5_0)),k2_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_33]),c_0_23])])).

fof(c_0_47,plain,(
    ! [X7,X8,X9] :
      ( ( r1_xboole_0(X7,k2_xboole_0(X8,X9))
        | ~ r1_xboole_0(X7,X8)
        | ~ r1_xboole_0(X7,X9) )
      & ( r1_xboole_0(X7,X8)
        | ~ r1_xboole_0(X7,k2_xboole_0(X8,X9)) )
      & ( r1_xboole_0(X7,X9)
        | ~ r1_xboole_0(X7,k2_xboole_0(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_48,negated_conjecture,
    ( k2_xboole_0(k2_struct_0(esk6_0),k2_struct_0(esk5_0)) = k2_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_49,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk6_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk6_0),k2_struct_0(esk5_0)) = u1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_23])])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_33]),c_0_23])])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(X1,k2_struct_0(esk5_0))
    | ~ r1_xboole_0(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_33]),c_0_34])])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),k2_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_22]),c_0_23])])).

cnf(c_0_58,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_49]),c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk5_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk5_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_33]),c_0_57])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tsep_1(esk5_0,esk7_0)
    | ~ r1_tsep_1(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_63,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_33]),c_0_34])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tsep_1(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_65,negated_conjecture,
    ( ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_63]),c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_33]),c_0_57])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_33]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.43  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.21/0.43  # and selection function SelectNewComplexAHPNS.
% 0.21/0.43  #
% 0.21/0.43  # Preprocessing time       : 0.028 s
% 0.21/0.43  
% 0.21/0.43  # Proof found!
% 0.21/0.43  # SZS status Theorem
% 0.21/0.43  # SZS output start CNFRefutation
% 0.21/0.43  fof(t23_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 0.21/0.43  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.21/0.43  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.43  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.21/0.43  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.21/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.43  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.43  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.21/0.43  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.21/0.43  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.21/0.43  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.21/0.43  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))))))))), inference(assume_negation,[status(cth)],[t23_tmap_1])).
% 0.21/0.43  fof(c_0_12, plain, ![X16, X17, X18, X20, X22]:(((r1_tarski(k2_struct_0(X17),k2_struct_0(X16))|~m1_pre_topc(X17,X16)|~l1_pre_topc(X17)|~l1_pre_topc(X16))&((((m1_subset_1(esk1_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))|~r2_hidden(X18,u1_pre_topc(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~m1_pre_topc(X17,X16)|~l1_pre_topc(X17)|~l1_pre_topc(X16))&(r2_hidden(esk1_3(X16,X17,X18),u1_pre_topc(X16))|~r2_hidden(X18,u1_pre_topc(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~m1_pre_topc(X17,X16)|~l1_pre_topc(X17)|~l1_pre_topc(X16)))&(X18=k9_subset_1(u1_struct_0(X17),esk1_3(X16,X17,X18),k2_struct_0(X17))|~r2_hidden(X18,u1_pre_topc(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~m1_pre_topc(X17,X16)|~l1_pre_topc(X17)|~l1_pre_topc(X16)))&(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X16)))|~r2_hidden(X20,u1_pre_topc(X16))|X18!=k9_subset_1(u1_struct_0(X17),X20,k2_struct_0(X17))|r2_hidden(X18,u1_pre_topc(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~m1_pre_topc(X17,X16)|~l1_pre_topc(X17)|~l1_pre_topc(X16))))&((m1_subset_1(esk2_2(X16,X17),k1_zfmisc_1(u1_struct_0(X17)))|~r1_tarski(k2_struct_0(X17),k2_struct_0(X16))|m1_pre_topc(X17,X16)|~l1_pre_topc(X17)|~l1_pre_topc(X16))&((~r2_hidden(esk2_2(X16,X17),u1_pre_topc(X17))|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X16)))|~r2_hidden(X22,u1_pre_topc(X16))|esk2_2(X16,X17)!=k9_subset_1(u1_struct_0(X17),X22,k2_struct_0(X17)))|~r1_tarski(k2_struct_0(X17),k2_struct_0(X16))|m1_pre_topc(X17,X16)|~l1_pre_topc(X17)|~l1_pre_topc(X16))&(((m1_subset_1(esk3_2(X16,X17),k1_zfmisc_1(u1_struct_0(X16)))|r2_hidden(esk2_2(X16,X17),u1_pre_topc(X17))|~r1_tarski(k2_struct_0(X17),k2_struct_0(X16))|m1_pre_topc(X17,X16)|~l1_pre_topc(X17)|~l1_pre_topc(X16))&(r2_hidden(esk3_2(X16,X17),u1_pre_topc(X16))|r2_hidden(esk2_2(X16,X17),u1_pre_topc(X17))|~r1_tarski(k2_struct_0(X17),k2_struct_0(X16))|m1_pre_topc(X17,X16)|~l1_pre_topc(X17)|~l1_pre_topc(X16)))&(esk2_2(X16,X17)=k9_subset_1(u1_struct_0(X17),esk3_2(X16,X17),k2_struct_0(X17))|r2_hidden(esk2_2(X16,X17),u1_pre_topc(X17))|~r1_tarski(k2_struct_0(X17),k2_struct_0(X16))|m1_pre_topc(X17,X16)|~l1_pre_topc(X17)|~l1_pre_topc(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.21/0.43  fof(c_0_13, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_pre_topc(X26,X25)|l1_pre_topc(X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.43  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk4_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk4_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk4_0))&(m1_pre_topc(esk5_0,esk6_0)&((~r1_tsep_1(esk5_0,esk7_0)|~r1_tsep_1(esk7_0,esk5_0))&(r1_tsep_1(esk6_0,esk7_0)|r1_tsep_1(esk7_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.21/0.43  cnf(c_0_15, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.43  cnf(c_0_16, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.43  cnf(c_0_17, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.43  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.43  fof(c_0_19, plain, ![X36, X37]:(~l1_struct_0(X36)|~l1_struct_0(X37)|(~r1_tsep_1(X36,X37)|r1_tsep_1(X37,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.21/0.43  fof(c_0_20, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X14,X13)|r1_tarski(k2_xboole_0(X12,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.21/0.43  cnf(c_0_21, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.43  cnf(c_0_22, negated_conjecture, (m1_pre_topc(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.43  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.21/0.43  fof(c_0_24, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.43  cnf(c_0_25, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.43  cnf(c_0_26, negated_conjecture, (r1_tsep_1(esk6_0,esk7_0)|r1_tsep_1(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.43  fof(c_0_27, plain, ![X24]:(~l1_pre_topc(X24)|l1_struct_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.43  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.43  cnf(c_0_29, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.43  cnf(c_0_30, negated_conjecture, (r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.21/0.43  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.43  cnf(c_0_32, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)|~l1_struct_0(esk7_0)|~l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.43  cnf(c_0_33, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.43  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_28]), c_0_18])])).
% 0.21/0.43  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_xboole_0(X1,k2_struct_0(esk5_0)),k2_struct_0(esk6_0))|~r1_tarski(X1,k2_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.43  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.21/0.43  fof(c_0_37, plain, ![X10, X11]:r1_tarski(X10,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.21/0.43  fof(c_0_38, plain, ![X15]:(~l1_struct_0(X15)|k2_struct_0(X15)=u1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.21/0.43  fof(c_0_39, plain, ![X31, X32]:((~r1_tsep_1(X31,X32)|r1_xboole_0(u1_struct_0(X31),u1_struct_0(X32))|~l1_struct_0(X32)|~l1_struct_0(X31))&(~r1_xboole_0(u1_struct_0(X31),u1_struct_0(X32))|r1_tsep_1(X31,X32)|~l1_struct_0(X32)|~l1_struct_0(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.21/0.43  cnf(c_0_40, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)|~l1_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.21/0.43  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.43  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_xboole_0(k2_struct_0(esk6_0),k2_struct_0(esk5_0)),k2_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.43  cnf(c_0_43, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.43  cnf(c_0_44, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.43  cnf(c_0_45, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.43  cnf(c_0_46, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_33]), c_0_23])])).
% 0.21/0.43  fof(c_0_47, plain, ![X7, X8, X9]:((r1_xboole_0(X7,k2_xboole_0(X8,X9))|~r1_xboole_0(X7,X8)|~r1_xboole_0(X7,X9))&((r1_xboole_0(X7,X8)|~r1_xboole_0(X7,k2_xboole_0(X8,X9)))&(r1_xboole_0(X7,X9)|~r1_xboole_0(X7,k2_xboole_0(X8,X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.21/0.43  cnf(c_0_48, negated_conjecture, (k2_xboole_0(k2_struct_0(esk6_0),k2_struct_0(esk5_0))=k2_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.21/0.43  cnf(c_0_49, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_44, c_0_33])).
% 0.21/0.43  cnf(c_0_50, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))|~l1_struct_0(esk6_0)|~l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.43  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.43  cnf(c_0_52, negated_conjecture, (k2_xboole_0(u1_struct_0(esk6_0),k2_struct_0(esk5_0))=u1_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_23])])).
% 0.21/0.43  cnf(c_0_53, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))|~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_33]), c_0_23])])).
% 0.21/0.43  cnf(c_0_54, negated_conjecture, (r1_xboole_0(X1,k2_struct_0(esk5_0))|~r1_xboole_0(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.43  cnf(c_0_55, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_33]), c_0_34])])).
% 0.21/0.43  cnf(c_0_56, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),k2_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.43  cnf(c_0_57, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_22]), c_0_23])])).
% 0.21/0.43  cnf(c_0_58, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.43  cnf(c_0_59, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_49]), c_0_57])])).
% 0.21/0.43  cnf(c_0_60, negated_conjecture, (r1_tsep_1(esk7_0,esk5_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.43  cnf(c_0_61, negated_conjecture, (r1_tsep_1(esk7_0,esk5_0)|~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_33]), c_0_57])])).
% 0.21/0.43  cnf(c_0_62, negated_conjecture, (~r1_tsep_1(esk5_0,esk7_0)|~r1_tsep_1(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.43  cnf(c_0_63, negated_conjecture, (r1_tsep_1(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_33]), c_0_34])])).
% 0.21/0.43  cnf(c_0_64, negated_conjecture, (~r1_tsep_1(esk5_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 0.21/0.43  cnf(c_0_65, negated_conjecture, (~l1_struct_0(esk5_0)|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_63]), c_0_64])).
% 0.21/0.43  cnf(c_0_66, negated_conjecture, (~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_33]), c_0_57])])).
% 0.21/0.43  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_33]), c_0_34])]), ['proof']).
% 0.21/0.43  # SZS output end CNFRefutation
% 0.21/0.43  # Proof object total steps             : 68
% 0.21/0.43  # Proof object clause steps            : 45
% 0.21/0.43  # Proof object formula steps           : 23
% 0.21/0.43  # Proof object conjectures             : 33
% 0.21/0.43  # Proof object clause conjectures      : 30
% 0.21/0.43  # Proof object formula conjectures     : 3
% 0.21/0.43  # Proof object initial clauses used    : 18
% 0.21/0.43  # Proof object initial formulas used   : 11
% 0.21/0.43  # Proof object generating inferences   : 24
% 0.21/0.43  # Proof object simplifying inferences  : 35
% 0.21/0.43  # Training examples: 0 positive, 0 negative
% 0.21/0.43  # Parsed axioms                        : 13
% 0.21/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.43  # Initial clauses                      : 41
% 0.21/0.43  # Removed in clause preprocessing      : 0
% 0.21/0.43  # Initial clauses in saturation        : 41
% 0.21/0.43  # Processed clauses                    : 530
% 0.21/0.43  # ...of these trivial                  : 18
% 0.21/0.43  # ...subsumed                          : 56
% 0.21/0.43  # ...remaining for further processing  : 456
% 0.21/0.43  # Other redundant clauses eliminated   : 4
% 0.21/0.43  # Clauses deleted for lack of memory   : 0
% 0.21/0.43  # Backward-subsumed                    : 5
% 0.21/0.43  # Backward-rewritten                   : 10
% 0.21/0.43  # Generated clauses                    : 2889
% 0.21/0.43  # ...of the previous two non-trivial   : 2698
% 0.21/0.43  # Contextual simplify-reflections      : 8
% 0.21/0.43  # Paramodulations                      : 2885
% 0.21/0.43  # Factorizations                       : 0
% 0.21/0.43  # Equation resolutions                 : 4
% 0.21/0.43  # Propositional unsat checks           : 0
% 0.21/0.43  #    Propositional check models        : 0
% 0.21/0.43  #    Propositional check unsatisfiable : 0
% 0.21/0.43  #    Propositional clauses             : 0
% 0.21/0.43  #    Propositional clauses after purity: 0
% 0.21/0.43  #    Propositional unsat core size     : 0
% 0.21/0.43  #    Propositional preprocessing time  : 0.000
% 0.21/0.43  #    Propositional encoding time       : 0.000
% 0.21/0.43  #    Propositional solver time         : 0.000
% 0.21/0.43  #    Success case prop preproc time    : 0.000
% 0.21/0.43  #    Success case prop encoding time   : 0.000
% 0.21/0.43  #    Success case prop solver time     : 0.000
% 0.21/0.43  # Current number of processed clauses  : 437
% 0.21/0.43  #    Positive orientable unit clauses  : 111
% 0.21/0.43  #    Positive unorientable unit clauses: 0
% 0.21/0.43  #    Negative unit clauses             : 6
% 0.21/0.43  #    Non-unit-clauses                  : 320
% 0.21/0.43  # Current number of unprocessed clauses: 2206
% 0.21/0.43  # ...number of literals in the above   : 7622
% 0.21/0.43  # Current number of archived formulas  : 0
% 0.21/0.43  # Current number of archived clauses   : 15
% 0.21/0.43  # Clause-clause subsumption calls (NU) : 3873
% 0.21/0.43  # Rec. Clause-clause subsumption calls : 3005
% 0.21/0.43  # Non-unit clause-clause subsumptions  : 69
% 0.21/0.43  # Unit Clause-clause subsumption calls : 1638
% 0.21/0.43  # Rewrite failures with RHS unbound    : 0
% 0.21/0.43  # BW rewrite match attempts            : 208
% 0.21/0.43  # BW rewrite match successes           : 7
% 0.21/0.43  # Condensation attempts                : 530
% 0.21/0.43  # Condensation successes               : 0
% 0.21/0.43  # Termbank termtop insertions          : 84081
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.079 s
% 0.21/0.43  # System time              : 0.007 s
% 0.21/0.43  # Total time               : 0.086 s
% 0.21/0.43  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
