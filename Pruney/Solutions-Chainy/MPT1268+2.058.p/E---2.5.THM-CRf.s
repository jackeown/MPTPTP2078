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
% DateTime   : Thu Dec  3 11:12:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 235 expanded)
%              Number of clauses        :   41 (  88 expanded)
%              Number of leaves         :   11 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  223 (1490 expanded)
%              Number of equality atoms :   34 ( 193 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,negated_conjecture,(
    ! [X37] :
      ( v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ v2_tops_1(esk3_0,esk2_0) )
      & ( r1_tarski(esk4_0,esk3_0)
        | ~ v2_tops_1(esk3_0,esk2_0) )
      & ( v3_pre_topc(esk4_0,esk2_0)
        | ~ v2_tops_1(esk3_0,esk2_0) )
      & ( esk4_0 != k1_xboole_0
        | ~ v2_tops_1(esk3_0,esk2_0) )
      & ( v2_tops_1(esk3_0,esk2_0)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ r1_tarski(X37,esk3_0)
        | ~ v3_pre_topc(X37,esk2_0)
        | X37 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).

fof(c_0_14,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X32,X33] :
      ( ( ~ v2_tops_1(X33,X32)
        | k1_tops_1(X32,X33) = k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) )
      & ( k1_tops_1(X32,X33) != k1_xboole_0
        | v2_tops_1(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

cnf(c_0_18,negated_conjecture,
    ( v2_tops_1(esk3_0,esk2_0)
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0)
    | ~ v3_pre_topc(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_22,plain,(
    ! [X25,X26,X27] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ r1_tarski(X26,X27)
      | r1_tarski(k1_tops_1(X25,X26),k1_tops_1(X25,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_23,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X28,X29,X30,X31] :
      ( ( ~ v3_pre_topc(X31,X29)
        | k1_tops_1(X29,X31) = X31
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X29)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( k1_tops_1(X28,X30) != X30
        | v3_pre_topc(X30,X28)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X29)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_26,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_tops_1(esk3_0,esk2_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_28,plain,(
    ! [X21,X22] :
      ( ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | v3_pre_topc(k1_tops_1(X21,X22),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_29,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | r1_tarski(k1_tops_1(X23,X24),X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = k1_xboole_0
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_24])])).

cnf(c_0_32,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_tops_1(esk3_0,esk2_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,X1),k1_xboole_0)
    | ~ v2_tops_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24]),c_0_16])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v2_tops_1(esk3_0,esk2_0)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_24]),c_0_34])])).

cnf(c_0_41,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,plain,
    ( v2_tops_1(X2,X1)
    | k1_tops_1(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( k1_tops_1(esk2_0,X1) = k1_xboole_0
    | v2_tops_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_24]),c_0_34])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_16]),c_0_24])])).

fof(c_0_45,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk4_0),k1_xboole_0)
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_33]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k1_tops_1(esk2_0,esk4_0) = esk4_0
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_33]),c_0_24])]),c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( v2_tops_1(esk3_0,esk2_0)
    | k1_tops_1(esk2_0,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_16]),c_0_24])])).

cnf(c_0_49,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_16]),c_0_44])]),c_0_31])).

fof(c_0_50,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | ~ r1_tarski(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_51,plain,(
    ! [X15,X17,X18,X19,X20] :
      ( ( r2_hidden(esk1_1(X15),X15)
        | X15 = k1_xboole_0 )
      & ( ~ r2_hidden(X17,X15)
        | esk1_1(X15) != k4_mcart_1(X17,X18,X19,X20)
        | X15 = k1_xboole_0 )
      & ( ~ r2_hidden(X18,X15)
        | esk1_1(X15) != k4_mcart_1(X17,X18,X19,X20)
        | X15 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk4_0,k1_xboole_0)
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v2_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_59,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,esk1_1(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_54])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.027 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t86_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 0.20/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.39  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.39  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 0.20/0.39  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.20/0.39  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 0.20/0.39  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.20/0.39  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.20/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.39  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 0.20/0.39  fof(c_0_11, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t86_tops_1])).
% 0.20/0.39  fof(c_0_12, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.39  fof(c_0_13, negated_conjecture, ![X37]:((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v2_tops_1(esk3_0,esk2_0))&(((r1_tarski(esk4_0,esk3_0)|~v2_tops_1(esk3_0,esk2_0))&(v3_pre_topc(esk4_0,esk2_0)|~v2_tops_1(esk3_0,esk2_0)))&(esk4_0!=k1_xboole_0|~v2_tops_1(esk3_0,esk2_0))))&(v2_tops_1(esk3_0,esk2_0)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk2_0)))|(~r1_tarski(X37,esk3_0)|~v3_pre_topc(X37,esk2_0)|X37=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).
% 0.20/0.39  fof(c_0_14, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.39  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  fof(c_0_17, plain, ![X32, X33]:((~v2_tops_1(X33,X32)|k1_tops_1(X32,X33)=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))&(k1_tops_1(X32,X33)!=k1_xboole_0|v2_tops_1(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (v2_tops_1(esk3_0,esk2_0)|X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)|~v3_pre_topc(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_19, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_20, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.39  fof(c_0_22, plain, ![X25, X26, X27]:(~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|(~r1_tarski(X26,X27)|r1_tarski(k1_tops_1(X25,X26),k1_tops_1(X25,X27)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.20/0.39  cnf(c_0_23, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  fof(c_0_25, plain, ![X28, X29, X30, X31]:((~v3_pre_topc(X31,X29)|k1_tops_1(X29,X31)=X31|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X29)|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(k1_tops_1(X28,X30)!=X30|v3_pre_topc(X30,X28)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X29)|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (X1=k1_xboole_0|v2_tops_1(esk3_0,esk2_0)|~v3_pre_topc(X1,esk2_0)|~r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.39  fof(c_0_28, plain, ![X21, X22]:(~v2_pre_topc(X21)|~l1_pre_topc(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v3_pre_topc(k1_tops_1(X21,X22),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.20/0.39  fof(c_0_29, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|r1_tarski(k1_tops_1(X23,X24),X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.20/0.39  cnf(c_0_30, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=k1_xboole_0|~v2_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_16]), c_0_24])])).
% 0.20/0.39  cnf(c_0_32, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v2_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (X1=k1_xboole_0|v2_tops_1(esk3_0,esk2_0)|~v3_pre_topc(X1,esk2_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.39  cnf(c_0_36, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_37, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,X1),k1_xboole_0)|~v2_tops_1(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_24]), c_0_16])])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~v2_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (k1_tops_1(X1,X2)=X2|~v2_tops_1(esk3_0,esk2_0)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_24]), c_0_34])])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|~v2_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_42, plain, (v2_tops_1(X2,X1)|k1_tops_1(X1,X2)!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (k1_tops_1(esk2_0,X1)=k1_xboole_0|v2_tops_1(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_24]), c_0_34])])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_16]), c_0_24])])).
% 0.20/0.39  fof(c_0_45, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk4_0),k1_xboole_0)|~v2_tops_1(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_33]), c_0_39])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (k1_tops_1(esk2_0,esk4_0)=esk4_0|~v2_tops_1(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_33]), c_0_24])]), c_0_41])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (v2_tops_1(esk3_0,esk2_0)|k1_tops_1(esk2_0,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_16]), c_0_24])])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_16]), c_0_44])]), c_0_31])).
% 0.20/0.39  fof(c_0_50, plain, ![X13, X14]:(~r2_hidden(X13,X14)|~r1_tarski(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.39  fof(c_0_51, plain, ![X15, X17, X18, X19, X20]:((r2_hidden(esk1_1(X15),X15)|X15=k1_xboole_0)&((~r2_hidden(X17,X15)|esk1_1(X15)!=k4_mcart_1(X17,X18,X19,X20)|X15=k1_xboole_0)&(~r2_hidden(X18,X15)|esk1_1(X15)!=k4_mcart_1(X17,X18,X19,X20)|X15=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 0.20/0.39  cnf(c_0_52, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (r1_tarski(esk4_0,k1_xboole_0)|~v2_tops_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (v2_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])])).
% 0.20/0.39  cnf(c_0_55, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.39  cnf(c_0_56, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.39  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_20, c_0_52])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (esk4_0!=k1_xboole_0|~v2_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_60, plain, (X1=k1_xboole_0|~r1_tarski(X1,esk1_1(X1))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_54])])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 64
% 0.20/0.39  # Proof object clause steps            : 41
% 0.20/0.39  # Proof object formula steps           : 23
% 0.20/0.39  # Proof object conjectures             : 30
% 0.20/0.39  # Proof object clause conjectures      : 27
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 20
% 0.20/0.39  # Proof object initial formulas used   : 11
% 0.20/0.39  # Proof object generating inferences   : 18
% 0.20/0.39  # Proof object simplifying inferences  : 29
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 11
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 23
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 23
% 0.20/0.39  # Processed clauses                    : 216
% 0.20/0.39  # ...of these trivial                  : 5
% 0.20/0.39  # ...subsumed                          : 86
% 0.20/0.39  # ...remaining for further processing  : 125
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 27
% 0.20/0.39  # Backward-rewritten                   : 40
% 0.20/0.39  # Generated clauses                    : 368
% 0.20/0.39  # ...of the previous two non-trivial   : 295
% 0.20/0.39  # Contextual simplify-reflections      : 8
% 0.20/0.39  # Paramodulations                      : 368
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 58
% 0.20/0.39  #    Positive orientable unit clauses  : 12
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 43
% 0.20/0.39  # Current number of unprocessed clauses: 88
% 0.20/0.39  # ...number of literals in the above   : 310
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 67
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 2468
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 1517
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 94
% 0.20/0.39  # Unit Clause-clause subsumption calls : 184
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 8
% 0.20/0.39  # BW rewrite match successes           : 8
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 7291
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.038 s
% 0.20/0.39  # System time              : 0.006 s
% 0.20/0.39  # Total time               : 0.043 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
