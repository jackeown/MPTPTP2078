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

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 140 expanded)
%              Number of clauses        :   39 (  56 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  321 ( 938 expanded)
%              Number of equality atoms :   24 (  77 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(c_0_16,plain,(
    ! [X7] : m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_17,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_18,negated_conjecture,(
    ! [X36] :
      ( ~ v2_struct_0(esk6_0)
      & v2_pre_topc(esk6_0)
      & l1_pre_topc(esk6_0)
      & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
      & m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))
      & ( v3_pre_topc(X36,esk6_0)
        | ~ r2_hidden(X36,esk8_0)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk6_0))) )
      & ( v4_pre_topc(X36,esk6_0)
        | ~ r2_hidden(X36,esk8_0)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk6_0))) )
      & ( r2_hidden(esk7_0,X36)
        | ~ r2_hidden(X36,esk8_0)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk6_0))) )
      & ( ~ v3_pre_topc(X36,esk6_0)
        | ~ v4_pre_topc(X36,esk6_0)
        | ~ r2_hidden(esk7_0,X36)
        | r2_hidden(X36,esk8_0)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk6_0))) )
      & esk8_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

fof(c_0_19,plain,(
    ! [X27,X28] :
      ( ( ~ v3_pre_topc(X28,X27)
        | r2_hidden(X28,u1_pre_topc(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( ~ r2_hidden(X28,u1_pre_topc(X27))
        | v3_pre_topc(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ v3_pre_topc(X1,esk6_0)
    | ~ v4_pre_topc(X1,esk6_0)
    | ~ r2_hidden(esk7_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_26,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r1_tarski(X20,u1_pre_topc(X19))
        | r2_hidden(k5_setfam_1(u1_struct_0(X19),X20),u1_pre_topc(X19))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(X21,u1_pre_topc(X19))
        | ~ r2_hidden(X22,u1_pre_topc(X19))
        | r2_hidden(k9_subset_1(u1_struct_0(X19),X21,X22),u1_pre_topc(X19))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | m1_subset_1(esk2_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk4_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | m1_subset_1(esk2_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk3_1(X19),u1_pre_topc(X19))
        | m1_subset_1(esk2_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk4_1(X19),u1_pre_topc(X19))
        | m1_subset_1(esk2_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X19),esk3_1(X19),esk4_1(X19)),u1_pre_topc(X19))
        | m1_subset_1(esk2_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | r1_tarski(esk2_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk4_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | r1_tarski(esk2_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk3_1(X19),u1_pre_topc(X19))
        | r1_tarski(esk2_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk4_1(X19),u1_pre_topc(X19))
        | r1_tarski(esk2_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X19),esk3_1(X19),esk4_1(X19)),u1_pre_topc(X19))
        | r1_tarski(esk2_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk2_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk4_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk2_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk3_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk2_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk4_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk2_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X19),esk3_1(X19),esk4_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk2_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v4_pre_topc(X1,esk6_0)
    | ~ v3_pre_topc(X1,esk6_0)
    | ~ r2_hidden(esk7_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(pm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X30] :
      ( ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | v4_pre_topc(k2_struct_0(X30),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).

fof(c_0_31,plain,(
    ! [X26] :
      ( ~ l1_struct_0(X26)
      | k2_struct_0(X26) = u1_struct_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk6_0),k1_xboole_0)
    | ~ v4_pre_topc(u1_struct_0(esk6_0),esk6_0)
    | ~ v3_pre_topc(u1_struct_0(esk6_0),esk6_0)
    | ~ r2_hidden(esk7_0,u1_struct_0(esk6_0)) ),
    inference(pm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_33,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( v4_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | ~ v1_xboole_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_39,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | ~ r1_tarski(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk6_0),k1_xboole_0)
    | ~ v4_pre_topc(u1_struct_0(esk6_0),esk6_0)
    | ~ r2_hidden(esk7_0,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_41,plain,
    ( v4_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_42,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X15,X17,X18] :
      ( ( r2_hidden(esk1_1(X15),X15)
        | X15 = k1_xboole_0 )
      & ( ~ r2_hidden(X17,X15)
        | esk1_1(X15) != k4_tarski(X17,X18)
        | X15 = k1_xboole_0 )
      & ( ~ r2_hidden(X18,X15)
        | esk1_1(X15) != k4_tarski(X17,X18)
        | X15 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk6_0),k1_xboole_0)
    | ~ l1_struct_0(esk6_0)
    | ~ r2_hidden(esk7_0,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40,c_0_41]),c_0_34]),c_0_35])])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_48,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_43,c_0_25])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( ~ l1_struct_0(esk6_0)
    | ~ r2_hidden(esk7_0,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_54,plain,(
    ! [X31] :
      ( ( m1_subset_1(esk5_1(X31),k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ v1_xboole_0(esk5_1(X31))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( v3_pre_topc(esk5_1(X31),X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( v4_pre_topc(esk5_1(X31),X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_tops_1])])])])])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

fof(c_0_57,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_43,c_0_50])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( u1_struct_0(esk6_0) = k1_xboole_0
    | ~ l1_struct_0(esk6_0) ),
    inference(pm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( esk5_1(X1) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(pm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_60,c_0_61]),c_0_35])])).

cnf(c_0_64,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_65,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk5_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( esk5_1(esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_34]),c_0_35])]),c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_67]),c_0_64]),c_0_34]),c_0_35])]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:10:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.18/0.39  # and selection function NoSelection.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.053 s
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(t28_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 0.18/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.18/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.18/0.39  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.18/0.39  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.18/0.39  fof(fc4_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v4_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 0.18/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.18/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.18/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.18/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.39  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.18/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.18/0.39  fof(rc3_tops_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:(((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v3_pre_topc(X2,X1))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 0.18/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t28_connsp_2])).
% 0.18/0.39  fof(c_0_16, plain, ![X7]:m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.18/0.39  fof(c_0_17, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.18/0.39  fof(c_0_18, negated_conjecture, ![X36]:(((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))&(((((v3_pre_topc(X36,esk6_0)|~r2_hidden(X36,esk8_0)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk6_0))))&(v4_pre_topc(X36,esk6_0)|~r2_hidden(X36,esk8_0)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk6_0)))))&(r2_hidden(esk7_0,X36)|~r2_hidden(X36,esk8_0)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk6_0)))))&(~v3_pre_topc(X36,esk6_0)|~v4_pre_topc(X36,esk6_0)|~r2_hidden(esk7_0,X36)|r2_hidden(X36,esk8_0)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk6_0)))))&esk8_0=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).
% 0.18/0.39  fof(c_0_19, plain, ![X27, X28]:((~v3_pre_topc(X28,X27)|r2_hidden(X28,u1_pre_topc(X27))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))&(~r2_hidden(X28,u1_pre_topc(X27))|v3_pre_topc(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.18/0.39  cnf(c_0_20, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.39  cnf(c_0_21, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.39  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,esk8_0)|~v3_pre_topc(X1,esk6_0)|~v4_pre_topc(X1,esk6_0)|~r2_hidden(esk7_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.39  cnf(c_0_23, negated_conjecture, (esk8_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.39  cnf(c_0_24, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.39  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.39  fof(c_0_26, plain, ![X19, X20, X21, X22]:((((r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))|~v2_pre_topc(X19)|~l1_pre_topc(X19))&(~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|(~r1_tarski(X20,u1_pre_topc(X19))|r2_hidden(k5_setfam_1(u1_struct_0(X19),X20),u1_pre_topc(X19)))|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|(~r2_hidden(X21,u1_pre_topc(X19))|~r2_hidden(X22,u1_pre_topc(X19))|r2_hidden(k9_subset_1(u1_struct_0(X19),X21,X22),u1_pre_topc(X19))))|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(((m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(m1_subset_1(esk2_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&((m1_subset_1(esk4_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(m1_subset_1(esk2_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(((r2_hidden(esk3_1(X19),u1_pre_topc(X19))|(m1_subset_1(esk2_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(r2_hidden(esk4_1(X19),u1_pre_topc(X19))|(m1_subset_1(esk2_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r2_hidden(k9_subset_1(u1_struct_0(X19),esk3_1(X19),esk4_1(X19)),u1_pre_topc(X19))|(m1_subset_1(esk2_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))))&(((m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(r1_tarski(esk2_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&((m1_subset_1(esk4_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(r1_tarski(esk2_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(((r2_hidden(esk3_1(X19),u1_pre_topc(X19))|(r1_tarski(esk2_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(r2_hidden(esk4_1(X19),u1_pre_topc(X19))|(r1_tarski(esk2_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r2_hidden(k9_subset_1(u1_struct_0(X19),esk3_1(X19),esk4_1(X19)),u1_pre_topc(X19))|(r1_tarski(esk2_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))))&((m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk2_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&((m1_subset_1(esk4_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk2_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(((r2_hidden(esk3_1(X19),u1_pre_topc(X19))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk2_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(r2_hidden(esk4_1(X19),u1_pre_topc(X19))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk2_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r2_hidden(k9_subset_1(u1_struct_0(X19),esk3_1(X19),esk4_1(X19)),u1_pre_topc(X19))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk2_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.18/0.39  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~v4_pre_topc(X1,esk6_0)|~v3_pre_topc(X1,esk6_0)|~r2_hidden(esk7_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.39  cnf(c_0_28, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(pm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.39  cnf(c_0_29, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.39  fof(c_0_30, plain, ![X30]:(~v2_pre_topc(X30)|~l1_pre_topc(X30)|v4_pre_topc(k2_struct_0(X30),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).
% 0.18/0.39  fof(c_0_31, plain, ![X26]:(~l1_struct_0(X26)|k2_struct_0(X26)=u1_struct_0(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.18/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(u1_struct_0(esk6_0),k1_xboole_0)|~v4_pre_topc(u1_struct_0(esk6_0),esk6_0)|~v3_pre_topc(u1_struct_0(esk6_0),esk6_0)|~r2_hidden(esk7_0,u1_struct_0(esk6_0))), inference(pm,[status(thm)],[c_0_27, c_0_25])).
% 0.18/0.39  cnf(c_0_33, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.39  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.39  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.39  cnf(c_0_36, plain, (v4_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.39  cnf(c_0_37, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.39  fof(c_0_38, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|~v1_xboole_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.18/0.39  fof(c_0_39, plain, ![X13, X14]:(~r2_hidden(X13,X14)|~r1_tarski(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.18/0.39  cnf(c_0_40, negated_conjecture, (r2_hidden(u1_struct_0(esk6_0),k1_xboole_0)|~v4_pre_topc(u1_struct_0(esk6_0),esk6_0)|~r2_hidden(esk7_0,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 0.18/0.40  cnf(c_0_41, plain, (v4_pre_topc(u1_struct_0(X1),X1)|~l1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.40  fof(c_0_42, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.40  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.40  fof(c_0_44, plain, ![X15, X17, X18]:((r2_hidden(esk1_1(X15),X15)|X15=k1_xboole_0)&((~r2_hidden(X17,X15)|esk1_1(X15)!=k4_tarski(X17,X18)|X15=k1_xboole_0)&(~r2_hidden(X18,X15)|esk1_1(X15)!=k4_tarski(X17,X18)|X15=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.18/0.40  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.40  cnf(c_0_46, negated_conjecture, (r2_hidden(u1_struct_0(esk6_0),k1_xboole_0)|~l1_struct_0(esk6_0)|~r2_hidden(esk7_0,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40, c_0_41]), c_0_34]), c_0_35])])).
% 0.18/0.40  cnf(c_0_47, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.40  fof(c_0_48, plain, ![X8, X9]:(~m1_subset_1(X8,X9)|(v1_xboole_0(X9)|r2_hidden(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.18/0.40  cnf(c_0_49, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_43, c_0_25])).
% 0.18/0.40  cnf(c_0_50, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.40  cnf(c_0_51, negated_conjecture, (~l1_struct_0(esk6_0)|~r2_hidden(esk7_0,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.18/0.40  cnf(c_0_52, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.40  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.40  fof(c_0_54, plain, ![X31]:((((m1_subset_1(esk5_1(X31),k1_zfmisc_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(~v1_xboole_0(esk5_1(X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))))&(v3_pre_topc(esk5_1(X31),X31)|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))))&(v4_pre_topc(esk5_1(X31),X31)|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_tops_1])])])])])).
% 0.18/0.40  cnf(c_0_55, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_49, c_0_50])).
% 0.18/0.40  cnf(c_0_56, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|~l1_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.18/0.40  fof(c_0_57, plain, ![X29]:(~l1_pre_topc(X29)|l1_struct_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.40  cnf(c_0_58, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_43, c_0_50])).
% 0.18/0.40  cnf(c_0_59, plain, (m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.40  cnf(c_0_60, negated_conjecture, (u1_struct_0(esk6_0)=k1_xboole_0|~l1_struct_0(esk6_0)), inference(pm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.40  cnf(c_0_61, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.18/0.40  cnf(c_0_62, plain, (esk5_1(X1)=k1_xboole_0|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(pm,[status(thm)],[c_0_58, c_0_59])).
% 0.18/0.40  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_60, c_0_61]), c_0_35])])).
% 0.18/0.40  cnf(c_0_64, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.40  cnf(c_0_65, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.40  cnf(c_0_66, plain, (v2_struct_0(X1)|~v1_xboole_0(esk5_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.40  cnf(c_0_67, negated_conjecture, (esk5_1(esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_34]), c_0_35])]), c_0_65])).
% 0.18/0.40  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_67]), c_0_64]), c_0_34]), c_0_35])]), c_0_65]), ['proof']).
% 0.18/0.40  # SZS output end CNFRefutation
% 0.18/0.40  # Proof object total steps             : 69
% 0.18/0.40  # Proof object clause steps            : 39
% 0.18/0.40  # Proof object formula steps           : 30
% 0.18/0.40  # Proof object conjectures             : 19
% 0.18/0.40  # Proof object clause conjectures      : 16
% 0.18/0.40  # Proof object formula conjectures     : 3
% 0.18/0.40  # Proof object initial clauses used    : 21
% 0.18/0.40  # Proof object initial formulas used   : 15
% 0.18/0.40  # Proof object generating inferences   : 16
% 0.18/0.40  # Proof object simplifying inferences  : 24
% 0.18/0.40  # Training examples: 0 positive, 0 negative
% 0.18/0.40  # Parsed axioms                        : 15
% 0.18/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.40  # Initial clauses                      : 47
% 0.18/0.40  # Removed in clause preprocessing      : 1
% 0.18/0.40  # Initial clauses in saturation        : 46
% 0.18/0.40  # Processed clauses                    : 98
% 0.18/0.40  # ...of these trivial                  : 0
% 0.18/0.40  # ...subsumed                          : 11
% 0.18/0.40  # ...remaining for further processing  : 87
% 0.18/0.40  # Other redundant clauses eliminated   : 0
% 0.18/0.40  # Clauses deleted for lack of memory   : 0
% 0.18/0.40  # Backward-subsumed                    : 4
% 0.18/0.40  # Backward-rewritten                   : 24
% 0.18/0.40  # Generated clauses                    : 126
% 0.18/0.40  # ...of the previous two non-trivial   : 121
% 0.18/0.40  # Contextual simplify-reflections      : 0
% 0.18/0.40  # Paramodulations                      : 126
% 0.18/0.40  # Factorizations                       : 0
% 0.18/0.40  # Equation resolutions                 : 0
% 0.18/0.40  # Propositional unsat checks           : 0
% 0.18/0.40  #    Propositional check models        : 0
% 0.18/0.40  #    Propositional check unsatisfiable : 0
% 0.18/0.40  #    Propositional clauses             : 0
% 0.18/0.40  #    Propositional clauses after purity: 0
% 0.18/0.40  #    Propositional unsat core size     : 0
% 0.18/0.40  #    Propositional preprocessing time  : 0.000
% 0.18/0.40  #    Propositional encoding time       : 0.000
% 0.18/0.40  #    Propositional solver time         : 0.000
% 0.18/0.40  #    Success case prop preproc time    : 0.000
% 0.18/0.40  #    Success case prop encoding time   : 0.000
% 0.18/0.40  #    Success case prop solver time     : 0.000
% 0.18/0.40  # Current number of processed clauses  : 59
% 0.18/0.40  #    Positive orientable unit clauses  : 12
% 0.18/0.40  #    Positive unorientable unit clauses: 0
% 0.18/0.40  #    Negative unit clauses             : 3
% 0.18/0.40  #    Non-unit-clauses                  : 44
% 0.18/0.40  # Current number of unprocessed clauses: 65
% 0.18/0.40  # ...number of literals in the above   : 259
% 0.18/0.40  # Current number of archived formulas  : 0
% 0.18/0.40  # Current number of archived clauses   : 29
% 0.18/0.40  # Clause-clause subsumption calls (NU) : 376
% 0.18/0.40  # Rec. Clause-clause subsumption calls : 242
% 0.18/0.40  # Non-unit clause-clause subsumptions  : 11
% 0.18/0.40  # Unit Clause-clause subsumption calls : 58
% 0.18/0.40  # Rewrite failures with RHS unbound    : 0
% 0.18/0.40  # BW rewrite match attempts            : 3
% 0.18/0.40  # BW rewrite match successes           : 3
% 0.18/0.40  # Condensation attempts                : 0
% 0.18/0.40  # Condensation successes               : 0
% 0.18/0.40  # Termbank termtop insertions          : 4427
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.058 s
% 0.18/0.40  # System time              : 0.008 s
% 0.18/0.40  # Total time               : 0.066 s
% 0.18/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
