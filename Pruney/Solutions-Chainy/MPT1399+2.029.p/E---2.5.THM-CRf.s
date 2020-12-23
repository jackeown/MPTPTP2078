%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:38 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 397 expanded)
%              Number of clauses        :   42 ( 158 expanded)
%              Number of leaves         :   16 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  307 (2665 expanded)
%              Number of equality atoms :   25 ( 195 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r2_hidden(X4,X3)
                      <=> ( v3_pre_topc(X4,X1)
                          & v4_pre_topc(X4,X1)
                          & r2_hidden(X2,X4) ) ) )
                  & X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc4_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v4_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(rc5_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v2_tops_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_tops_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(fc14_tops_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ~ v2_tops_1(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ~ ( ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r2_hidden(X4,X3)
                        <=> ( v3_pre_topc(X4,X1)
                            & v4_pre_topc(X4,X1)
                            & r2_hidden(X2,X4) ) ) )
                    & X3 = k1_xboole_0 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_connsp_2])).

fof(c_0_17,negated_conjecture,(
    ! [X38] :
      ( ~ v2_struct_0(esk6_0)
      & v2_pre_topc(esk6_0)
      & l1_pre_topc(esk6_0)
      & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
      & m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))
      & ( v3_pre_topc(X38,esk6_0)
        | ~ r2_hidden(X38,esk8_0)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(esk6_0))) )
      & ( v4_pre_topc(X38,esk6_0)
        | ~ r2_hidden(X38,esk8_0)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(esk6_0))) )
      & ( r2_hidden(esk7_0,X38)
        | ~ r2_hidden(X38,esk8_0)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(esk6_0))) )
      & ( ~ v3_pre_topc(X38,esk6_0)
        | ~ v4_pre_topc(X38,esk6_0)
        | ~ r2_hidden(esk7_0,X38)
        | r2_hidden(X38,esk8_0)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(esk6_0))) )
      & esk8_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).

fof(c_0_18,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,X15)
      | ~ r1_tarski(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_19,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ v3_pre_topc(X1,esk6_0)
    | ~ v4_pre_topc(X1,esk6_0)
    | ~ r2_hidden(esk7_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v4_pre_topc(X1,esk6_0)
    | ~ v3_pre_topc(X1,esk6_0)
    | ~ r2_hidden(esk7_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_26,plain,(
    ! [X31] :
      ( ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | v4_pre_topc(k2_struct_0(X31),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).

fof(c_0_27,plain,(
    ! [X27] :
      ( ~ l1_struct_0(X27)
      | k2_struct_0(X27) = u1_struct_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_28,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_29,plain,(
    ! [X8] : m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_30,plain,(
    ! [X7] : k2_subset_1(X7) = X7 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_31,negated_conjecture,
    ( ~ v4_pre_topc(X1,esk6_0)
    | ~ v3_pre_topc(X1,esk6_0)
    | ~ r2_hidden(esk7_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( v4_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X9,X10)
      | v1_xboole_0(X10)
      | r2_hidden(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_40,negated_conjecture,
    ( ~ v3_pre_topc(k2_struct_0(esk6_0),esk6_0)
    | ~ r2_hidden(esk7_0,k2_struct_0(esk6_0))
    | ~ m1_subset_1(k2_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_41,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_43,plain,(
    ! [X28,X29] :
      ( ( ~ v3_pre_topc(X29,X28)
        | r2_hidden(X29,u1_pre_topc(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( ~ r2_hidden(X29,u1_pre_topc(X28))
        | v3_pre_topc(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_44,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk6_0),esk6_0)
    | ~ r2_hidden(esk7_0,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_34])])).

cnf(c_0_48,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_49,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r1_tarski(X21,u1_pre_topc(X20))
        | r2_hidden(k5_setfam_1(u1_struct_0(X20),X21),u1_pre_topc(X20))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(X22,u1_pre_topc(X20))
        | ~ r2_hidden(X23,u1_pre_topc(X20))
        | r2_hidden(k9_subset_1(u1_struct_0(X20),X22,X23),u1_pre_topc(X20))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk3_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk3_1(X20),u1_pre_topc(X20))
        | m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk4_1(X20),u1_pre_topc(X20))
        | m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X20),esk3_1(X20),esk4_1(X20)),u1_pre_topc(X20))
        | m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk3_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | r1_tarski(esk2_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | r1_tarski(esk2_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk3_1(X20),u1_pre_topc(X20))
        | r1_tarski(esk2_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk4_1(X20),u1_pre_topc(X20))
        | r1_tarski(esk2_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X20),esk3_1(X20),esk4_1(X20)),u1_pre_topc(X20))
        | r1_tarski(esk2_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk3_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk3_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk4_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X20),esk3_1(X20),esk4_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk6_0))
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))
    | ~ r2_hidden(esk7_0,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_34]),c_0_42])])).

cnf(c_0_53,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_54,plain,(
    ! [X32] :
      ( ( m1_subset_1(esk5_1(X32),k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) )
      & ( v2_tops_1(esk5_1(X32),X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc5_tops_1])])])])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk6_0) = k1_xboole_0
    | r2_hidden(esk7_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk7_0,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_33]),c_0_34])])).

fof(c_0_57,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | ~ v1_xboole_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_58,plain,
    ( m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[c_0_51,c_0_56])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk5_1(esk6_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_34])])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_59])).

fof(c_0_64,plain,(
    ! [X16,X18,X19] :
      ( ( r2_hidden(esk1_1(X16),X16)
        | X16 = k1_xboole_0 )
      & ( ~ r2_hidden(X18,X16)
        | esk1_1(X16) != k4_tarski(X18,X19)
        | X16 = k1_xboole_0 )
      & ( ~ r2_hidden(X19,X16)
        | esk1_1(X16) != k4_tarski(X18,X19)
        | X16 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

fof(c_0_65,plain,(
    ! [X34] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | ~ v2_tops_1(k2_struct_0(X34),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_tops_1])])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_67,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tops_1(k2_struct_0(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_69,plain,
    ( v2_tops_1(esk5_1(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_70,negated_conjecture,
    ( esk5_1(esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | ~ v2_tops_1(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_41])).

cnf(c_0_72,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_34])])).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_59]),c_0_72]),c_0_33]),c_0_34])]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.037 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t28_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 0.20/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.39  fof(fc4_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v4_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 0.20/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.39  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.20/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.39  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.20/0.39  fof(rc5_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v2_tops_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc5_tops_1)).
% 0.20/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.39  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.20/0.39  fof(fc14_tops_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>~(v2_tops_1(k2_struct_0(X1),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_tops_1)).
% 0.20/0.39  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t28_connsp_2])).
% 0.20/0.39  fof(c_0_17, negated_conjecture, ![X38]:(((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))&(((((v3_pre_topc(X38,esk6_0)|~r2_hidden(X38,esk8_0)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(esk6_0))))&(v4_pre_topc(X38,esk6_0)|~r2_hidden(X38,esk8_0)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(esk6_0)))))&(r2_hidden(esk7_0,X38)|~r2_hidden(X38,esk8_0)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(esk6_0)))))&(~v3_pre_topc(X38,esk6_0)|~v4_pre_topc(X38,esk6_0)|~r2_hidden(esk7_0,X38)|r2_hidden(X38,esk8_0)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(esk6_0)))))&esk8_0=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).
% 0.20/0.39  fof(c_0_18, plain, ![X14, X15]:(~r2_hidden(X14,X15)|~r1_tarski(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.39  fof(c_0_19, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,esk8_0)|~v3_pre_topc(X1,esk6_0)|~v4_pre_topc(X1,esk6_0)|~r2_hidden(esk7_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (esk8_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_23, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~v4_pre_topc(X1,esk6_0)|~v3_pre_topc(X1,esk6_0)|~r2_hidden(esk7_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.39  cnf(c_0_25, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.39  fof(c_0_26, plain, ![X31]:(~v2_pre_topc(X31)|~l1_pre_topc(X31)|v4_pre_topc(k2_struct_0(X31),X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).
% 0.20/0.39  fof(c_0_27, plain, ![X27]:(~l1_struct_0(X27)|k2_struct_0(X27)=u1_struct_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.39  fof(c_0_28, plain, ![X30]:(~l1_pre_topc(X30)|l1_struct_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.39  fof(c_0_29, plain, ![X8]:m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.39  fof(c_0_30, plain, ![X7]:k2_subset_1(X7)=X7, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (~v4_pre_topc(X1,esk6_0)|~v3_pre_topc(X1,esk6_0)|~r2_hidden(esk7_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(sr,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.39  cnf(c_0_32, plain, (v4_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_35, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_37, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_38, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  fof(c_0_39, plain, ![X9, X10]:(~m1_subset_1(X9,X10)|(v1_xboole_0(X10)|r2_hidden(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (~v3_pre_topc(k2_struct_0(esk6_0),esk6_0)|~r2_hidden(esk7_0,k2_struct_0(esk6_0))|~m1_subset_1(k2_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.20/0.39  cnf(c_0_41, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.39  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.39  fof(c_0_43, plain, ![X28, X29]:((~v3_pre_topc(X29,X28)|r2_hidden(X29,u1_pre_topc(X28))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(~r2_hidden(X29,u1_pre_topc(X28))|v3_pre_topc(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.20/0.39  fof(c_0_44, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.39  cnf(c_0_45, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk6_0),esk6_0)|~r2_hidden(esk7_0,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_34])])).
% 0.20/0.39  cnf(c_0_48, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  fof(c_0_49, plain, ![X20, X21, X22, X23]:((((r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))|~v2_pre_topc(X20)|~l1_pre_topc(X20))&(~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|(~r1_tarski(X21,u1_pre_topc(X20))|r2_hidden(k5_setfam_1(u1_struct_0(X20),X21),u1_pre_topc(X20)))|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))|(~r2_hidden(X22,u1_pre_topc(X20))|~r2_hidden(X23,u1_pre_topc(X20))|r2_hidden(k9_subset_1(u1_struct_0(X20),X22,X23),u1_pre_topc(X20))))|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(((m1_subset_1(esk3_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&((m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(((r2_hidden(esk3_1(X20),u1_pre_topc(X20))|(m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(r2_hidden(esk4_1(X20),u1_pre_topc(X20))|(m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r2_hidden(k9_subset_1(u1_struct_0(X20),esk3_1(X20),esk4_1(X20)),u1_pre_topc(X20))|(m1_subset_1(esk2_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))))&(((m1_subset_1(esk3_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(r1_tarski(esk2_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&((m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(r1_tarski(esk2_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(((r2_hidden(esk3_1(X20),u1_pre_topc(X20))|(r1_tarski(esk2_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(r2_hidden(esk4_1(X20),u1_pre_topc(X20))|(r1_tarski(esk2_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r2_hidden(k9_subset_1(u1_struct_0(X20),esk3_1(X20),esk4_1(X20)),u1_pre_topc(X20))|(r1_tarski(esk2_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))))&((m1_subset_1(esk3_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&((m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(((r2_hidden(esk3_1(X20),u1_pre_topc(X20))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(r2_hidden(esk4_1(X20),u1_pre_topc(X20))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r2_hidden(k9_subset_1(u1_struct_0(X20),esk3_1(X20),esk4_1(X20)),u1_pre_topc(X20))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk2_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.20/0.39  cnf(c_0_50, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk6_0))|v1_xboole_0(u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (~r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))|~r2_hidden(esk7_0,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_34]), c_0_42])])).
% 0.20/0.39  cnf(c_0_53, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.39  fof(c_0_54, plain, ![X32]:((m1_subset_1(esk5_1(X32),k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))&(v2_tops_1(esk5_1(X32),X32)|~l1_pre_topc(X32))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc5_tops_1])])])])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk6_0)=k1_xboole_0|r2_hidden(esk7_0,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk7_0,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_33]), c_0_34])])).
% 0.20/0.39  fof(c_0_57, plain, ![X11, X12, X13]:(~r2_hidden(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X13))|~v1_xboole_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.39  cnf(c_0_58, plain, (m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (u1_struct_0(esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))), inference(sr,[status(thm)],[c_0_51, c_0_56])).
% 0.20/0.39  cnf(c_0_61, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk5_1(esk6_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_34])])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_60, c_0_59])).
% 0.20/0.39  fof(c_0_64, plain, ![X16, X18, X19]:((r2_hidden(esk1_1(X16),X16)|X16=k1_xboole_0)&((~r2_hidden(X18,X16)|esk1_1(X16)!=k4_tarski(X18,X19)|X16=k1_xboole_0)&(~r2_hidden(X19,X16)|esk1_1(X16)!=k4_tarski(X18,X19)|X16=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.20/0.39  fof(c_0_65, plain, ![X34]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~v2_tops_1(k2_struct_0(X34),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_tops_1])])])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (~r2_hidden(X1,esk5_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])])).
% 0.20/0.39  cnf(c_0_67, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.39  cnf(c_0_68, plain, (v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tops_1(k2_struct_0(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.39  cnf(c_0_69, plain, (v2_tops_1(esk5_1(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (esk5_1(esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.39  cnf(c_0_71, plain, (v2_struct_0(X1)|~v2_tops_1(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_68, c_0_41])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (v2_tops_1(k1_xboole_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_34])])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_59]), c_0_72]), c_0_33]), c_0_34])]), c_0_73]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 75
% 0.20/0.39  # Proof object clause steps            : 42
% 0.20/0.39  # Proof object formula steps           : 33
% 0.20/0.39  # Proof object conjectures             : 25
% 0.20/0.39  # Proof object clause conjectures      : 22
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 22
% 0.20/0.39  # Proof object initial formulas used   : 16
% 0.20/0.39  # Proof object generating inferences   : 14
% 0.20/0.39  # Proof object simplifying inferences  : 29
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 16
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 46
% 0.20/0.39  # Removed in clause preprocessing      : 1
% 0.20/0.39  # Initial clauses in saturation        : 45
% 0.20/0.39  # Processed clauses                    : 147
% 0.20/0.39  # ...of these trivial                  : 2
% 0.20/0.39  # ...subsumed                          : 25
% 0.20/0.39  # ...remaining for further processing  : 120
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 13
% 0.20/0.39  # Generated clauses                    : 83
% 0.20/0.39  # ...of the previous two non-trivial   : 84
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 79
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
% 0.20/0.39  #    Positive orientable unit clauses  : 13
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 42
% 0.20/0.39  # Current number of unprocessed clauses: 19
% 0.20/0.39  # ...number of literals in the above   : 84
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 63
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 1858
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 515
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 8
% 0.20/0.39  # Unit Clause-clause subsumption calls : 23
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 2
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 5274
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.048 s
% 0.20/0.40  # System time              : 0.005 s
% 0.20/0.40  # Total time               : 0.052 s
% 0.20/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
