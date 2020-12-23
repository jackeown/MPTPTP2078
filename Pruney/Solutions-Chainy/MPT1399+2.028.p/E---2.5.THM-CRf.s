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
% DateTime   : Thu Dec  3 11:14:38 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 154 expanded)
%              Number of clauses        :   40 (  61 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  315 ( 992 expanded)
%              Number of equality atoms :   22 (  75 expanded)
%              Maximal formula depth    :   27 (   5 average)
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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(rc3_tops_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v3_pre_topc(X2,X1)
          & v4_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,negated_conjecture,(
    ! [X40] :
      ( ~ v2_struct_0(esk7_0)
      & v2_pre_topc(esk7_0)
      & l1_pre_topc(esk7_0)
      & m1_subset_1(esk8_0,u1_struct_0(esk7_0))
      & m1_subset_1(esk9_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))
      & ( v3_pre_topc(X40,esk7_0)
        | ~ r2_hidden(X40,esk9_0)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(esk7_0))) )
      & ( v4_pre_topc(X40,esk7_0)
        | ~ r2_hidden(X40,esk9_0)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(esk7_0))) )
      & ( r2_hidden(esk8_0,X40)
        | ~ r2_hidden(X40,esk9_0)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(esk7_0))) )
      & ( ~ v3_pre_topc(X40,esk7_0)
        | ~ v4_pre_topc(X40,esk7_0)
        | ~ r2_hidden(esk8_0,X40)
        | r2_hidden(X40,esk9_0)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(esk7_0))) )
      & esk9_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

fof(c_0_17,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | ~ r1_tarski(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_18,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ v4_pre_topc(X1,esk7_0)
    | ~ r2_hidden(esk8_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v4_pre_topc(X1,esk7_0)
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
    ! [X34] :
      ( ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | v4_pre_topc(k2_struct_0(X34),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).

fof(c_0_26,plain,(
    ! [X11] : m1_subset_1(k2_subset_1(X11),k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_27,plain,(
    ! [X10] : k2_subset_1(X10) = X10 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_28,negated_conjecture,
    ( ~ v4_pre_topc(X1,esk7_0)
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(sr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( v4_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_32,plain,(
    ! [X30] :
      ( ~ l1_struct_0(X30)
      | k2_struct_0(X30) = u1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_33,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_36,plain,(
    ! [X19,X21,X22] :
      ( ( r2_hidden(esk2_1(X19),X19)
        | X19 = k1_xboole_0 )
      & ( ~ r2_hidden(X21,X19)
        | esk2_1(X19) != k4_tarski(X21,X22)
        | X19 = k1_xboole_0 )
      & ( ~ r2_hidden(X22,X19)
        | esk2_1(X19) != k4_tarski(X21,X22)
        | X19 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

fof(c_0_37,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,X13)
      | v1_xboole_0(X13)
      | r2_hidden(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_38,negated_conjecture,
    ( ~ v3_pre_topc(k2_struct_0(esk7_0),esk7_0)
    | ~ m1_subset_1(k2_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(esk8_0,k2_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_39,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_41,plain,(
    ! [X33] :
      ( ~ l1_pre_topc(X33)
      | l1_struct_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_42,plain,(
    ! [X23,X24,X25,X26] :
      ( ( r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ r1_tarski(X24,u1_pre_topc(X23))
        | r2_hidden(k5_setfam_1(u1_struct_0(X23),X24),u1_pre_topc(X23))
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r2_hidden(X25,u1_pre_topc(X23))
        | ~ r2_hidden(X26,u1_pre_topc(X23))
        | r2_hidden(k9_subset_1(u1_struct_0(X23),X25,X26),u1_pre_topc(X23))
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk4_1(X23),k1_zfmisc_1(u1_struct_0(X23)))
        | m1_subset_1(esk3_1(X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk5_1(X23),k1_zfmisc_1(u1_struct_0(X23)))
        | m1_subset_1(esk3_1(X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(esk4_1(X23),u1_pre_topc(X23))
        | m1_subset_1(esk3_1(X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(esk5_1(X23),u1_pre_topc(X23))
        | m1_subset_1(esk3_1(X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X23),esk4_1(X23),esk5_1(X23)),u1_pre_topc(X23))
        | m1_subset_1(esk3_1(X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk4_1(X23),k1_zfmisc_1(u1_struct_0(X23)))
        | r1_tarski(esk3_1(X23),u1_pre_topc(X23))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk5_1(X23),k1_zfmisc_1(u1_struct_0(X23)))
        | r1_tarski(esk3_1(X23),u1_pre_topc(X23))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(esk4_1(X23),u1_pre_topc(X23))
        | r1_tarski(esk3_1(X23),u1_pre_topc(X23))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(esk5_1(X23),u1_pre_topc(X23))
        | r1_tarski(esk3_1(X23),u1_pre_topc(X23))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X23),esk4_1(X23),esk5_1(X23)),u1_pre_topc(X23))
        | r1_tarski(esk3_1(X23),u1_pre_topc(X23))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk4_1(X23),k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X23),esk3_1(X23)),u1_pre_topc(X23))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk5_1(X23),k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X23),esk3_1(X23)),u1_pre_topc(X23))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(esk4_1(X23),u1_pre_topc(X23))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X23),esk3_1(X23)),u1_pre_topc(X23))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(esk5_1(X23),u1_pre_topc(X23))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X23),esk3_1(X23)),u1_pre_topc(X23))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X23),esk4_1(X23),esk5_1(X23)),u1_pre_topc(X23))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X23),esk3_1(X23)),u1_pre_topc(X23))
        | ~ r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_43,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk7_0),esk7_0)
    | ~ l1_struct_0(esk7_0)
    | ~ r2_hidden(esk8_0,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_48,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_49,plain,(
    ! [X31,X32] :
      ( ( ~ v3_pre_topc(X32,X31)
        | r2_hidden(X32,u1_pre_topc(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( ~ r2_hidden(X32,u1_pre_topc(X31))
        | v3_pre_topc(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_50,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk7_0))
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk7_0),esk7_0)
    | ~ r2_hidden(esk8_0,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_31])])).

cnf(c_0_54,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_30]),c_0_31])])).

fof(c_0_56,plain,(
    ! [X35] :
      ( ( m1_subset_1(esk6_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ v1_xboole_0(esk6_1(X35))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( v3_pre_topc(esk6_1(X35),X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( v4_pre_topc(esk6_1(X35),X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_tops_1])])])])])).

cnf(c_0_57,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | r2_hidden(esk8_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(esk8_0,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_31]),c_0_40]),c_0_55])])).

fof(c_0_59,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X16))
      | ~ v1_xboole_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk6_1(esk7_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_30]),c_0_61]),c_0_31])]),c_0_62])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk6_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( esk6_1(esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_44])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_30]),c_0_31]),c_0_66])]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:51:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.029 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t28_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 0.12/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.38  fof(fc4_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v4_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 0.12/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.12/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.12/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.12/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.38  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.12/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.12/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.38  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.12/0.38  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.12/0.38  fof(rc3_tops_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:(((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v3_pre_topc(X2,X1))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 0.12/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.12/0.38  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t28_connsp_2])).
% 0.12/0.38  fof(c_0_16, negated_conjecture, ![X40]:(((~v2_struct_0(esk7_0)&v2_pre_topc(esk7_0))&l1_pre_topc(esk7_0))&(m1_subset_1(esk8_0,u1_struct_0(esk7_0))&(m1_subset_1(esk9_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))&(((((v3_pre_topc(X40,esk7_0)|~r2_hidden(X40,esk9_0)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(esk7_0))))&(v4_pre_topc(X40,esk7_0)|~r2_hidden(X40,esk9_0)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(esk7_0)))))&(r2_hidden(esk8_0,X40)|~r2_hidden(X40,esk9_0)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(esk7_0)))))&(~v3_pre_topc(X40,esk7_0)|~v4_pre_topc(X40,esk7_0)|~r2_hidden(esk8_0,X40)|r2_hidden(X40,esk9_0)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(esk7_0)))))&esk9_0=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).
% 0.12/0.38  fof(c_0_17, plain, ![X17, X18]:(~r2_hidden(X17,X18)|~r1_tarski(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.38  fof(c_0_18, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,esk9_0)|~v3_pre_topc(X1,esk7_0)|~v4_pre_topc(X1,esk7_0)|~r2_hidden(esk8_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (esk9_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_22, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~v4_pre_topc(X1,esk7_0)|~v3_pre_topc(X1,esk7_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))|~r2_hidden(esk8_0,X1)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.38  cnf(c_0_24, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.38  fof(c_0_25, plain, ![X34]:(~v2_pre_topc(X34)|~l1_pre_topc(X34)|v4_pre_topc(k2_struct_0(X34),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).
% 0.12/0.38  fof(c_0_26, plain, ![X11]:m1_subset_1(k2_subset_1(X11),k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.12/0.38  fof(c_0_27, plain, ![X10]:k2_subset_1(X10)=X10, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (~v4_pre_topc(X1,esk7_0)|~v3_pre_topc(X1,esk7_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))|~r2_hidden(esk8_0,X1)), inference(sr,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.38  cnf(c_0_29, plain, (v4_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  fof(c_0_32, plain, ![X30]:(~l1_struct_0(X30)|k2_struct_0(X30)=u1_struct_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.12/0.38  cnf(c_0_33, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_34, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  fof(c_0_35, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.38  fof(c_0_36, plain, ![X19, X21, X22]:((r2_hidden(esk2_1(X19),X19)|X19=k1_xboole_0)&((~r2_hidden(X21,X19)|esk2_1(X19)!=k4_tarski(X21,X22)|X19=k1_xboole_0)&(~r2_hidden(X22,X19)|esk2_1(X19)!=k4_tarski(X21,X22)|X19=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.12/0.38  fof(c_0_37, plain, ![X12, X13]:(~m1_subset_1(X12,X13)|(v1_xboole_0(X13)|r2_hidden(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (~v3_pre_topc(k2_struct_0(esk7_0),esk7_0)|~m1_subset_1(k2_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(esk7_0)))|~r2_hidden(esk8_0,k2_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])])).
% 0.12/0.38  cnf(c_0_39, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.38  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.38  fof(c_0_41, plain, ![X33]:(~l1_pre_topc(X33)|l1_struct_0(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.38  fof(c_0_42, plain, ![X23, X24, X25, X26]:((((r2_hidden(u1_struct_0(X23),u1_pre_topc(X23))|~v2_pre_topc(X23)|~l1_pre_topc(X23))&(~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|(~r1_tarski(X24,u1_pre_topc(X23))|r2_hidden(k5_setfam_1(u1_struct_0(X23),X24),u1_pre_topc(X23)))|~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))|(~r2_hidden(X25,u1_pre_topc(X23))|~r2_hidden(X26,u1_pre_topc(X23))|r2_hidden(k9_subset_1(u1_struct_0(X23),X25,X26),u1_pre_topc(X23))))|~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(((m1_subset_1(esk4_1(X23),k1_zfmisc_1(u1_struct_0(X23)))|(m1_subset_1(esk3_1(X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23))&((m1_subset_1(esk5_1(X23),k1_zfmisc_1(u1_struct_0(X23)))|(m1_subset_1(esk3_1(X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23))&(((r2_hidden(esk4_1(X23),u1_pre_topc(X23))|(m1_subset_1(esk3_1(X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23))&(r2_hidden(esk5_1(X23),u1_pre_topc(X23))|(m1_subset_1(esk3_1(X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~r2_hidden(k9_subset_1(u1_struct_0(X23),esk4_1(X23),esk5_1(X23)),u1_pre_topc(X23))|(m1_subset_1(esk3_1(X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23)))))&(((m1_subset_1(esk4_1(X23),k1_zfmisc_1(u1_struct_0(X23)))|(r1_tarski(esk3_1(X23),u1_pre_topc(X23))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23))&((m1_subset_1(esk5_1(X23),k1_zfmisc_1(u1_struct_0(X23)))|(r1_tarski(esk3_1(X23),u1_pre_topc(X23))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23))&(((r2_hidden(esk4_1(X23),u1_pre_topc(X23))|(r1_tarski(esk3_1(X23),u1_pre_topc(X23))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23))&(r2_hidden(esk5_1(X23),u1_pre_topc(X23))|(r1_tarski(esk3_1(X23),u1_pre_topc(X23))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~r2_hidden(k9_subset_1(u1_struct_0(X23),esk4_1(X23),esk5_1(X23)),u1_pre_topc(X23))|(r1_tarski(esk3_1(X23),u1_pre_topc(X23))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23)))))&((m1_subset_1(esk4_1(X23),k1_zfmisc_1(u1_struct_0(X23)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X23),esk3_1(X23)),u1_pre_topc(X23))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23))&((m1_subset_1(esk5_1(X23),k1_zfmisc_1(u1_struct_0(X23)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X23),esk3_1(X23)),u1_pre_topc(X23))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23))&(((r2_hidden(esk4_1(X23),u1_pre_topc(X23))|(~r2_hidden(k5_setfam_1(u1_struct_0(X23),esk3_1(X23)),u1_pre_topc(X23))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23))&(r2_hidden(esk5_1(X23),u1_pre_topc(X23))|(~r2_hidden(k5_setfam_1(u1_struct_0(X23),esk3_1(X23)),u1_pre_topc(X23))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~r2_hidden(k9_subset_1(u1_struct_0(X23),esk4_1(X23),esk5_1(X23)),u1_pre_topc(X23))|(~r2_hidden(k5_setfam_1(u1_struct_0(X23),esk3_1(X23)),u1_pre_topc(X23))|~r2_hidden(u1_struct_0(X23),u1_pre_topc(X23)))|v2_pre_topc(X23)|~l1_pre_topc(X23)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.12/0.38  cnf(c_0_43, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.38  cnf(c_0_44, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.38  cnf(c_0_45, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk7_0),esk7_0)|~l1_struct_0(esk7_0)|~r2_hidden(esk8_0,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.12/0.38  cnf(c_0_48, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.38  fof(c_0_49, plain, ![X31, X32]:((~v3_pre_topc(X32,X31)|r2_hidden(X32,u1_pre_topc(X31))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))&(~r2_hidden(X32,u1_pre_topc(X31))|v3_pre_topc(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.12/0.38  cnf(c_0_50, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.38  cnf(c_0_51, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk7_0))|v1_xboole_0(u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk7_0),esk7_0)|~r2_hidden(esk8_0,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_31])])).
% 0.12/0.38  cnf(c_0_54, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_30]), c_0_31])])).
% 0.12/0.38  fof(c_0_56, plain, ![X35]:((((m1_subset_1(esk6_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~v1_xboole_0(esk6_1(X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35))))&(v3_pre_topc(esk6_1(X35),X35)|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35))))&(v4_pre_topc(esk6_1(X35),X35)|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_tops_1])])])])])).
% 0.12/0.38  cnf(c_0_57, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0|r2_hidden(esk8_0,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (~r2_hidden(esk8_0,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_31]), c_0_40]), c_0_55])])).
% 0.12/0.38  fof(c_0_59, plain, ![X14, X15, X16]:(~r2_hidden(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X16))|~v1_xboole_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.12/0.38  cnf(c_0_60, plain, (m1_subset_1(esk6_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk7_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_57, c_0_58])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_63, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.38  cnf(c_0_64, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk6_1(esk7_0),k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_30]), c_0_61]), c_0_31])]), c_0_62])).
% 0.12/0.38  cnf(c_0_66, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_63])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (~r2_hidden(X1,esk6_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 0.12/0.38  cnf(c_0_68, plain, (v2_struct_0(X1)|~v1_xboole_0(esk6_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.38  cnf(c_0_69, negated_conjecture, (esk6_1(esk7_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_44])).
% 0.12/0.38  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_30]), c_0_31]), c_0_66])]), c_0_62]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 71
% 0.12/0.38  # Proof object clause steps            : 40
% 0.12/0.38  # Proof object formula steps           : 31
% 0.12/0.38  # Proof object conjectures             : 23
% 0.12/0.38  # Proof object clause conjectures      : 20
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 22
% 0.12/0.38  # Proof object initial formulas used   : 15
% 0.12/0.38  # Proof object generating inferences   : 14
% 0.12/0.38  # Proof object simplifying inferences  : 28
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 15
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 48
% 0.12/0.38  # Removed in clause preprocessing      : 1
% 0.12/0.38  # Initial clauses in saturation        : 47
% 0.12/0.38  # Processed clauses                    : 117
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 12
% 0.12/0.38  # ...remaining for further processing  : 105
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 19
% 0.12/0.38  # Generated clauses                    : 57
% 0.12/0.38  # ...of the previous two non-trivial   : 67
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 55
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 36
% 0.12/0.38  #    Positive orientable unit clauses  : 11
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 3
% 0.12/0.38  #    Non-unit-clauses                  : 22
% 0.12/0.38  # Current number of unprocessed clauses: 39
% 0.12/0.38  # ...number of literals in the above   : 134
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 70
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 1510
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 337
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.12/0.38  # Unit Clause-clause subsumption calls : 40
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 4
% 0.12/0.38  # BW rewrite match successes           : 3
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 4904
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.032 s
% 0.12/0.38  # System time              : 0.007 s
% 0.12/0.38  # Total time               : 0.039 s
% 0.12/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
