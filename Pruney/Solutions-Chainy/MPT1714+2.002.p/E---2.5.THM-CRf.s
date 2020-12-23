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
% DateTime   : Thu Dec  3 11:16:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 714 expanded)
%              Number of clauses        :   62 ( 311 expanded)
%              Number of leaves         :   10 ( 164 expanded)
%              Depth                    :   17
%              Number of atoms          :  301 (4533 expanded)
%              Number of equality atoms :    5 (  20 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

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

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X19,X20] :
      ( ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | v2_pre_topc(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk3_0)
    & m1_pre_topc(esk4_0,esk5_0)
    & ( ~ r1_tsep_1(esk4_0,esk6_0)
      | ~ r1_tsep_1(esk6_0,esk4_0) )
    & ( r1_tsep_1(esk5_0,esk6_0)
      | r1_tsep_1(esk6_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_14,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | l1_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_15,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r1_tarski(u1_struct_0(X29),u1_struct_0(X30))
        | m1_pre_topc(X29,X30)
        | ~ m1_pre_topc(X30,X28)
        | ~ m1_pre_topc(X29,X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ m1_pre_topc(X29,X30)
        | r1_tarski(u1_struct_0(X29),u1_struct_0(X30))
        | ~ m1_pre_topc(X30,X28)
        | ~ m1_pre_topc(X29,X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_24,plain,(
    ! [X24,X25] :
      ( ( ~ r1_tsep_1(X24,X25)
        | r1_xboole_0(u1_struct_0(X24),u1_struct_0(X25))
        | ~ l1_struct_0(X25)
        | ~ l1_struct_0(X24) )
      & ( ~ r1_xboole_0(u1_struct_0(X24),u1_struct_0(X25))
        | r1_tsep_1(X24,X25)
        | ~ l1_struct_0(X25)
        | ~ l1_struct_0(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_28,plain,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_32,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_18]),c_0_19])])).

fof(c_0_36,plain,(
    ! [X26,X27] :
      ( ~ l1_struct_0(X26)
      | ~ l1_struct_0(X27)
      | ~ r1_tsep_1(X26,X27)
      | r1_tsep_1(X27,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

fof(c_0_37,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_38,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,plain,
    ( ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(X3,u1_struct_0(X2))
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_26])).

cnf(c_0_44,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r1_tsep_1(X1,X2)
    | r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X4)
    | ~ r1_tarski(X4,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk5_0))
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,plain,
    ( r1_tsep_1(X1,X2)
    | r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,plain,
    ( ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X3,X5)
    | ~ r1_tarski(X4,u1_struct_0(X2))
    | ~ r1_tarski(X5,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_51])).

cnf(c_0_58,plain,
    ( r1_tsep_1(X1,X2)
    | r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tsep_1(X1,esk5_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(X2,u1_struct_0(esk4_0))
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r1_tsep_1(esk6_0,X1)
    | ~ r1_tsep_1(X1,esk6_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_tsep_1(esk5_0,esk6_0)
    | r1_tsep_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_63,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(esk4_0)),u1_struct_0(esk4_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tsep_1(X1,esk5_0)
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(X2,u1_struct_0(esk4_0))
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_45]),c_0_34])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tsep_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_34])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( r1_tsep_1(esk6_0,esk4_0)
    | r2_hidden(esk2_2(u1_struct_0(esk6_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_57])).

cnf(c_0_69,plain,
    ( r1_tsep_1(X1,X2)
    | r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X1))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( ~ l1_struct_0(esk6_0)
    | ~ r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk6_0)
    | ~ r1_tsep_1(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_72,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk6_0)
    | r2_hidden(esk2_2(u1_struct_0(esk6_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_57])])).

cnf(c_0_73,plain,
    ( r1_tsep_1(X1,X2)
    | r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X1))
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_45])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_45]),c_0_57])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk2_2(u1_struct_0(esk6_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_68])).

cnf(c_0_76,plain,
    ( r1_tsep_1(X1,X2)
    | r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_45])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk2_2(u1_struct_0(esk6_0),u1_struct_0(esk4_0)),X1)
    | ~ r1_tarski(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( r1_tsep_1(esk6_0,X1)
    | r2_hidden(esk2_2(u1_struct_0(esk6_0),u1_struct_0(X1)),u1_struct_0(esk6_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_57])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(esk2_2(u1_struct_0(esk6_0),u1_struct_0(esk4_0)),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_22])).

cnf(c_0_80,negated_conjecture,
    ( r1_tsep_1(esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_59]),c_0_79])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_80])])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_80]),c_0_57])]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.56  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01BI
% 0.20/0.56  # and selection function PSelectMinOptimalNoXTypePred.
% 0.20/0.56  #
% 0.20/0.56  # Preprocessing time       : 0.029 s
% 0.20/0.56  # Presaturation interreduction done
% 0.20/0.56  
% 0.20/0.56  # Proof found!
% 0.20/0.56  # SZS status Theorem
% 0.20/0.56  # SZS output start CNFRefutation
% 0.20/0.56  fof(t23_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 0.20/0.56  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.56  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.56  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.56  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.20/0.56  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.56  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.20/0.56  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.56  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.20/0.56  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.56  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))))))))), inference(assume_negation,[status(cth)],[t23_tmap_1])).
% 0.20/0.56  fof(c_0_11, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.56  fof(c_0_12, plain, ![X19, X20]:(~v2_pre_topc(X19)|~l1_pre_topc(X19)|(~m1_pre_topc(X20,X19)|v2_pre_topc(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.56  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk3_0))&(m1_pre_topc(esk4_0,esk5_0)&((~r1_tsep_1(esk4_0,esk6_0)|~r1_tsep_1(esk6_0,esk4_0))&(r1_tsep_1(esk5_0,esk6_0)|r1_tsep_1(esk6_0,esk5_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.20/0.56  fof(c_0_14, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|l1_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.56  fof(c_0_15, plain, ![X28, X29, X30]:((~r1_tarski(u1_struct_0(X29),u1_struct_0(X30))|m1_pre_topc(X29,X30)|~m1_pre_topc(X30,X28)|~m1_pre_topc(X29,X28)|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(~m1_pre_topc(X29,X30)|r1_tarski(u1_struct_0(X29),u1_struct_0(X30))|~m1_pre_topc(X30,X28)|~m1_pre_topc(X29,X28)|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.20/0.56  cnf(c_0_16, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.56  cnf(c_0_17, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.56  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_20, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.56  cnf(c_0_21, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.56  cnf(c_0_22, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.56  fof(c_0_23, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk2_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk2_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.56  fof(c_0_24, plain, ![X24, X25]:((~r1_tsep_1(X24,X25)|r1_xboole_0(u1_struct_0(X24),u1_struct_0(X25))|~l1_struct_0(X25)|~l1_struct_0(X24))&(~r1_xboole_0(u1_struct_0(X24),u1_struct_0(X25))|r1_tsep_1(X24,X25)|~l1_struct_0(X25)|~l1_struct_0(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.20/0.56  cnf(c_0_25, negated_conjecture, (v2_pre_topc(X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.20/0.56  cnf(c_0_26, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_27, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 0.20/0.56  cnf(c_0_28, plain, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.56  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.56  cnf(c_0_30, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.56  fof(c_0_31, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.56  cnf(c_0_32, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.56  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.56  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.20/0.56  cnf(c_0_35, negated_conjecture, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_18]), c_0_19])])).
% 0.20/0.56  fof(c_0_36, plain, ![X26, X27]:(~l1_struct_0(X26)|~l1_struct_0(X27)|(~r1_tsep_1(X26,X27)|r1_tsep_1(X27,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.20/0.56  fof(c_0_37, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.56  cnf(c_0_38, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.56  cnf(c_0_39, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.56  cnf(c_0_40, plain, (~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)|~r2_hidden(X3,u1_struct_0(X2))|~r2_hidden(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.56  cnf(c_0_41, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.56  cnf(c_0_42, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,esk5_0)|~m1_pre_topc(X1,esk5_0)|~m1_pre_topc(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.20/0.56  cnf(c_0_43, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_26])).
% 0.20/0.56  cnf(c_0_44, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.56  cnf(c_0_45, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.56  cnf(c_0_46, plain, (r1_tsep_1(X1,X2)|r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.56  cnf(c_0_47, plain, (~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)|~r2_hidden(X3,u1_struct_0(X1))|~r2_hidden(X3,X4)|~r1_tarski(X4,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.56  cnf(c_0_48, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk5_0))|~m1_pre_topc(X1,esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.56  cnf(c_0_49, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_50, plain, (r1_tsep_1(X1,X2)|~r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.56  cnf(c_0_51, negated_conjecture, (m1_pre_topc(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_52, plain, (r1_tsep_1(X1,X2)|r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 0.20/0.56  cnf(c_0_53, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_54, plain, (~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)|~r2_hidden(X3,X4)|~r2_hidden(X3,X5)|~r1_tarski(X4,u1_struct_0(X2))|~r1_tarski(X5,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_47, c_0_41])).
% 0.20/0.56  cnf(c_0_55, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.56  cnf(c_0_56, plain, (r1_tsep_1(X1,X2)|~r1_tsep_1(X2,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_50, c_0_45])).
% 0.20/0.56  cnf(c_0_57, negated_conjecture, (l1_pre_topc(esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_51])).
% 0.20/0.56  cnf(c_0_58, plain, (r1_tsep_1(X1,X2)|r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X2))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_52, c_0_45])).
% 0.20/0.56  cnf(c_0_59, negated_conjecture, (l1_pre_topc(esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_53])).
% 0.20/0.56  cnf(c_0_60, negated_conjecture, (~r1_tsep_1(X1,esk5_0)|~l1_struct_0(esk5_0)|~l1_struct_0(X1)|~r2_hidden(X2,u1_struct_0(esk4_0))|~r2_hidden(X2,X3)|~r1_tarski(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.56  cnf(c_0_61, negated_conjecture, (r1_tsep_1(esk6_0,X1)|~r1_tsep_1(X1,esk6_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.56  cnf(c_0_62, negated_conjecture, (r1_tsep_1(esk5_0,esk6_0)|r1_tsep_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_63, negated_conjecture, (r1_tsep_1(X1,esk4_0)|r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(esk4_0)),u1_struct_0(esk4_0))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.56  cnf(c_0_64, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.56  cnf(c_0_65, negated_conjecture, (~r1_tsep_1(X1,esk5_0)|~l1_struct_0(X1)|~r2_hidden(X2,u1_struct_0(esk4_0))|~r2_hidden(X2,X3)|~r1_tarski(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_45]), c_0_34])])).
% 0.20/0.56  cnf(c_0_66, negated_conjecture, (r1_tsep_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_34])])).
% 0.20/0.56  cnf(c_0_67, negated_conjecture, (r1_tsep_1(esk4_0,X1)|~r1_tsep_1(X1,esk4_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_56, c_0_59])).
% 0.20/0.56  cnf(c_0_68, negated_conjecture, (r1_tsep_1(esk6_0,esk4_0)|r2_hidden(esk2_2(u1_struct_0(esk6_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_63, c_0_57])).
% 0.20/0.56  cnf(c_0_69, plain, (r1_tsep_1(X1,X2)|r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X1))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_38, c_0_64])).
% 0.20/0.56  cnf(c_0_70, negated_conjecture, (~l1_struct_0(esk6_0)|~r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,X2)|~r1_tarski(X2,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.56  cnf(c_0_71, negated_conjecture, (~r1_tsep_1(esk4_0,esk6_0)|~r1_tsep_1(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_72, negated_conjecture, (r1_tsep_1(esk4_0,esk6_0)|r2_hidden(esk2_2(u1_struct_0(esk6_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_57])])).
% 0.20/0.56  cnf(c_0_73, plain, (r1_tsep_1(X1,X2)|r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X1))|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_69, c_0_45])).
% 0.20/0.56  cnf(c_0_74, negated_conjecture, (~r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,X2)|~r1_tarski(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_45]), c_0_57])])).
% 0.20/0.56  cnf(c_0_75, negated_conjecture, (r2_hidden(esk2_2(u1_struct_0(esk6_0),u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_68])).
% 0.20/0.56  cnf(c_0_76, plain, (r1_tsep_1(X1,X2)|r2_hidden(esk2_2(u1_struct_0(X1),u1_struct_0(X2)),u1_struct_0(X1))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_73, c_0_45])).
% 0.20/0.56  cnf(c_0_77, negated_conjecture, (~r2_hidden(esk2_2(u1_struct_0(esk6_0),u1_struct_0(esk4_0)),X1)|~r1_tarski(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.56  cnf(c_0_78, negated_conjecture, (r1_tsep_1(esk6_0,X1)|r2_hidden(esk2_2(u1_struct_0(esk6_0),u1_struct_0(X1)),u1_struct_0(esk6_0))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_76, c_0_57])).
% 0.20/0.56  cnf(c_0_79, negated_conjecture, (~r2_hidden(esk2_2(u1_struct_0(esk6_0),u1_struct_0(esk4_0)),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_77, c_0_22])).
% 0.20/0.56  cnf(c_0_80, negated_conjecture, (r1_tsep_1(esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_59]), c_0_79])).
% 0.20/0.56  cnf(c_0_81, negated_conjecture, (~r1_tsep_1(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_80])])).
% 0.20/0.56  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_80]), c_0_57])]), c_0_81]), ['proof']).
% 0.20/0.56  # SZS output end CNFRefutation
% 0.20/0.56  # Proof object total steps             : 83
% 0.20/0.56  # Proof object clause steps            : 62
% 0.20/0.56  # Proof object formula steps           : 21
% 0.20/0.56  # Proof object conjectures             : 39
% 0.20/0.56  # Proof object clause conjectures      : 36
% 0.20/0.56  # Proof object formula conjectures     : 3
% 0.20/0.56  # Proof object initial clauses used    : 21
% 0.20/0.56  # Proof object initial formulas used   : 10
% 0.20/0.56  # Proof object generating inferences   : 39
% 0.20/0.56  # Proof object simplifying inferences  : 22
% 0.20/0.56  # Training examples: 0 positive, 0 negative
% 0.20/0.56  # Parsed axioms                        : 10
% 0.20/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.56  # Initial clauses                      : 29
% 0.20/0.56  # Removed in clause preprocessing      : 0
% 0.20/0.56  # Initial clauses in saturation        : 29
% 0.20/0.56  # Processed clauses                    : 1831
% 0.20/0.56  # ...of these trivial                  : 3
% 0.20/0.56  # ...subsumed                          : 957
% 0.20/0.56  # ...remaining for further processing  : 870
% 0.20/0.56  # Other redundant clauses eliminated   : 2
% 0.20/0.56  # Clauses deleted for lack of memory   : 0
% 0.20/0.56  # Backward-subsumed                    : 68
% 0.20/0.56  # Backward-rewritten                   : 12
% 0.20/0.56  # Generated clauses                    : 9766
% 0.20/0.56  # ...of the previous two non-trivial   : 9498
% 0.20/0.56  # Contextual simplify-reflections      : 9
% 0.20/0.56  # Paramodulations                      : 9764
% 0.20/0.56  # Factorizations                       : 0
% 0.20/0.56  # Equation resolutions                 : 2
% 0.20/0.56  # Propositional unsat checks           : 0
% 0.20/0.56  #    Propositional check models        : 0
% 0.20/0.56  #    Propositional check unsatisfiable : 0
% 0.20/0.56  #    Propositional clauses             : 0
% 0.20/0.56  #    Propositional clauses after purity: 0
% 0.20/0.56  #    Propositional unsat core size     : 0
% 0.20/0.56  #    Propositional preprocessing time  : 0.000
% 0.20/0.56  #    Propositional encoding time       : 0.000
% 0.20/0.56  #    Propositional solver time         : 0.000
% 0.20/0.56  #    Success case prop preproc time    : 0.000
% 0.20/0.56  #    Success case prop encoding time   : 0.000
% 0.20/0.56  #    Success case prop solver time     : 0.000
% 0.20/0.56  # Current number of processed clauses  : 760
% 0.20/0.56  #    Positive orientable unit clauses  : 31
% 0.20/0.56  #    Positive unorientable unit clauses: 0
% 0.20/0.56  #    Negative unit clauses             : 18
% 0.20/0.56  #    Non-unit-clauses                  : 711
% 0.20/0.56  # Current number of unprocessed clauses: 7654
% 0.20/0.56  # ...number of literals in the above   : 48007
% 0.20/0.56  # Current number of archived formulas  : 0
% 0.20/0.56  # Current number of archived clauses   : 108
% 0.20/0.56  # Clause-clause subsumption calls (NU) : 78713
% 0.20/0.56  # Rec. Clause-clause subsumption calls : 21292
% 0.20/0.56  # Non-unit clause-clause subsumptions  : 827
% 0.20/0.56  # Unit Clause-clause subsumption calls : 991
% 0.20/0.56  # Rewrite failures with RHS unbound    : 0
% 0.20/0.56  # BW rewrite match attempts            : 77
% 0.20/0.56  # BW rewrite match successes           : 11
% 0.20/0.56  # Condensation attempts                : 0
% 0.20/0.56  # Condensation successes               : 0
% 0.20/0.56  # Termbank termtop insertions          : 178165
% 0.20/0.56  
% 0.20/0.56  # -------------------------------------------------
% 0.20/0.56  # User time                : 0.203 s
% 0.20/0.56  # System time              : 0.012 s
% 0.20/0.56  # Total time               : 0.215 s
% 0.20/0.56  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
