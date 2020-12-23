%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:08 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 828 expanded)
%              Number of clauses        :   39 ( 317 expanded)
%              Number of leaves         :   12 ( 203 expanded)
%              Depth                    :   14
%              Number of atoms          :  250 (7441 expanded)
%              Number of equality atoms :   34 (1326 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   40 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_compts_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( X2 = k1_xboole_0
             => ( v2_compts_1(X2,X1)
              <=> v1_compts_1(k1_pre_topc(X1,X2)) ) )
            & ( v2_pre_topc(X1)
             => ( X2 = k1_xboole_0
                | ( v2_compts_1(X2,X1)
                <=> v1_compts_1(k1_pre_topc(X1,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t11_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X3,k2_struct_0(X2))
               => ( v2_compts_1(X3,X1)
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X4 = X3
                       => v2_compts_1(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t10_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_compts_1(X1)
      <=> v2_compts_1(k2_struct_0(X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ( X2 = k1_xboole_0
               => ( v2_compts_1(X2,X1)
                <=> v1_compts_1(k1_pre_topc(X1,X2)) ) )
              & ( v2_pre_topc(X1)
               => ( X2 = k1_xboole_0
                  | ( v2_compts_1(X2,X1)
                  <=> v1_compts_1(k1_pre_topc(X1,X2)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_compts_1])).

fof(c_0_13,plain,(
    ! [X10,X11] :
      ( ( v1_pre_topc(k1_pre_topc(X10,X11))
        | ~ l1_pre_topc(X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10))) )
      & ( m1_pre_topc(k1_pre_topc(X10,X11),X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( v2_pre_topc(esk2_0)
      | esk3_0 = k1_xboole_0 )
    & ( esk3_0 != k1_xboole_0
      | esk3_0 = k1_xboole_0 )
    & ( ~ v2_compts_1(esk3_0,esk2_0)
      | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
      | esk3_0 = k1_xboole_0 )
    & ( v2_compts_1(esk3_0,esk2_0)
      | v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
      | esk3_0 = k1_xboole_0 )
    & ( v2_pre_topc(esk2_0)
      | ~ v2_compts_1(esk3_0,esk2_0)
      | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) )
    & ( esk3_0 != k1_xboole_0
      | ~ v2_compts_1(esk3_0,esk2_0)
      | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) )
    & ( ~ v2_compts_1(esk3_0,esk2_0)
      | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
      | ~ v2_compts_1(esk3_0,esk2_0)
      | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) )
    & ( v2_compts_1(esk3_0,esk2_0)
      | v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
      | ~ v2_compts_1(esk3_0,esk2_0)
      | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) )
    & ( v2_pre_topc(esk2_0)
      | v2_compts_1(esk3_0,esk2_0)
      | v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) )
    & ( esk3_0 != k1_xboole_0
      | v2_compts_1(esk3_0,esk2_0)
      | v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) )
    & ( ~ v2_compts_1(esk3_0,esk2_0)
      | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
      | v2_compts_1(esk3_0,esk2_0)
      | v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) )
    & ( v2_compts_1(esk3_0,esk2_0)
      | v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
      | v2_compts_1(esk3_0,esk2_0)
      | v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | l1_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_16,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X21,X22,X23,X24] :
      ( ( ~ v2_compts_1(X23,X21)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | X24 != X23
        | v2_compts_1(X24,X22)
        | ~ r1_tarski(X23,k2_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk1_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X22)))
        | v2_compts_1(X23,X21)
        | ~ r1_tarski(X23,k2_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X21) )
      & ( esk1_3(X21,X22,X23) = X23
        | v2_compts_1(X23,X21)
        | ~ r1_tarski(X23,k2_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ v2_compts_1(esk1_3(X21,X22,X23),X22)
        | v2_compts_1(X23,X21)
        | ~ r1_tarski(X23,k2_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).

fof(c_0_20,plain,(
    ! [X17,X18,X19] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

fof(c_0_21,plain,(
    ! [X8] : m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_22,plain,(
    ! [X7] : k2_subset_1(X7) = X7 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_23,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_24,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | u1_struct_0(k1_pre_topc(X15,X16)) = X16 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

cnf(c_0_27,plain,
    ( v2_compts_1(X3,X4)
    | ~ v2_compts_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | X3 != X1
    | ~ r1_tarski(X1,k2_struct_0(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | k2_struct_0(X9) = u1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_32,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_18])])).

cnf(c_0_34,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_36,plain,(
    ! [X20] :
      ( ( ~ v1_compts_1(X20)
        | v2_compts_1(k2_struct_0(X20),X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ v2_compts_1(k2_struct_0(X20),X20)
        | v1_compts_1(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_compts_1])])])).

cnf(c_0_37,negated_conjecture,
    ( v2_compts_1(esk3_0,esk2_0)
    | v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
    | v2_compts_1(esk3_0,esk2_0)
    | v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,plain,
    ( v2_compts_1(X1,X2)
    | ~ v2_compts_1(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_27]),c_0_28])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( l1_struct_0(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk2_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_18])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( v2_compts_1(k2_struct_0(X1),X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v2_compts_1(esk3_0,esk2_0)
    | v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( v2_compts_1(u1_struct_0(X1),X1)
    | ~ v2_compts_1(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(u1_struct_0(X1),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_pre_topc(esk2_0,esk3_0))
    | v2_compts_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_33])])).

cnf(c_0_50,plain,
    ( v1_compts_1(X1)
    | ~ v2_compts_1(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))
    | ~ v2_compts_1(esk3_0,X1)
    | ~ m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_42]),c_0_42]),c_0_42]),c_0_48])])).

cnf(c_0_52,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))
    | v2_compts_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,esk2_0)
    | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
    | ~ v2_compts_1(esk3_0,esk2_0)
    | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,negated_conjecture,
    ( v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
    | ~ v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_47]),c_0_33])])).

cnf(c_0_55,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_25]),c_0_18])]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,esk2_0)
    | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_58,plain,
    ( esk1_3(X1,X2,X3) = X3
    | v2_compts_1(X3,X1)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( esk1_3(esk2_0,X1,esk3_0) = esk3_0
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ r1_tarski(esk3_0,k2_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_17]),c_0_18])]),c_0_59])).

cnf(c_0_61,plain,
    ( v2_compts_1(X3,X1)
    | ~ v2_compts_1(esk1_3(X1,X2,X3),X2)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_62,negated_conjecture,
    ( esk1_3(esk2_0,k1_pre_topc(esk2_0,esk3_0),esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_47]),c_0_25]),c_0_48])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_55]),c_0_25]),c_0_18]),c_0_17]),c_0_47]),c_0_48])]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0S
% 0.13/0.38  # and selection function SelectComplexG.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t12_compts_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((X2=k1_xboole_0=>(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2))))&(v2_pre_topc(X1)=>(X2=k1_xboole_0|(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_compts_1)).
% 0.13/0.38  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(t11_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,k2_struct_0(X2))=>(v2_compts_1(X3,X1)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X4=X3=>v2_compts_1(X4,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_compts_1)).
% 0.13/0.38  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.13/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.13/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t10_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_compts_1(X1)<=>v2_compts_1(k2_struct_0(X1),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_compts_1)).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((X2=k1_xboole_0=>(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2))))&(v2_pre_topc(X1)=>(X2=k1_xboole_0|(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2))))))))), inference(assume_negation,[status(cth)],[t12_compts_1])).
% 0.13/0.38  fof(c_0_13, plain, ![X10, X11]:((v1_pre_topc(k1_pre_topc(X10,X11))|(~l1_pre_topc(X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))))&(m1_pre_topc(k1_pre_topc(X10,X11),X10)|(~l1_pre_topc(X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.13/0.38  fof(c_0_14, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((v2_pre_topc(esk2_0)|esk3_0=k1_xboole_0)&((esk3_0!=k1_xboole_0|esk3_0=k1_xboole_0)&((~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|esk3_0=k1_xboole_0)&(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|esk3_0=k1_xboole_0))))&(((v2_pre_topc(esk2_0)|(~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&((esk3_0!=k1_xboole_0|(~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&((~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|(~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|(~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0)))))))&((v2_pre_topc(esk2_0)|(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&((esk3_0!=k1_xboole_0|(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&((~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X13, X14]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|l1_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  cnf(c_0_16, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_19, plain, ![X21, X22, X23, X24]:((~v2_compts_1(X23,X21)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(X24!=X23|v2_compts_1(X24,X22)))|~r1_tarski(X23,k2_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X21))&((m1_subset_1(esk1_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X22)))|v2_compts_1(X23,X21)|~r1_tarski(X23,k2_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X21))&((esk1_3(X21,X22,X23)=X23|v2_compts_1(X23,X21)|~r1_tarski(X23,k2_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X21))&(~v2_compts_1(esk1_3(X21,X22,X23),X22)|v2_compts_1(X23,X21)|~r1_tarski(X23,k2_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X17, X18, X19]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X8]:m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.38  fof(c_0_22, plain, ![X7]:k2_subset_1(X7)=X7, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.38  fof(c_0_23, plain, ![X12]:(~l1_pre_topc(X12)|l1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  cnf(c_0_24, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.13/0.38  fof(c_0_26, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|u1_struct_0(k1_pre_topc(X15,X16))=X16)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.13/0.38  cnf(c_0_27, plain, (v2_compts_1(X3,X4)|~v2_compts_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|X3!=X1|~r1_tarski(X1,k2_struct_0(X4))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X4,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_28, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_29, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_30, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  fof(c_0_31, plain, ![X9]:(~l1_struct_0(X9)|k2_struct_0(X9)=u1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.13/0.38  cnf(c_0_32, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (l1_pre_topc(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_18])])).
% 0.13/0.38  cnf(c_0_34, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  fof(c_0_35, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_36, plain, ![X20]:((~v1_compts_1(X20)|v2_compts_1(k2_struct_0(X20),X20)|~l1_pre_topc(X20))&(~v2_compts_1(k2_struct_0(X20),X20)|v1_compts_1(X20)|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_compts_1])])])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_38, plain, (v2_compts_1(X1,X2)|~v2_compts_1(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_27]), c_0_28])).
% 0.13/0.38  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.38  cnf(c_0_40, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (l1_struct_0(k1_pre_topc(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (u1_struct_0(k1_pre_topc(esk2_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_17]), c_0_18])])).
% 0.13/0.38  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_44, plain, (v2_compts_1(k2_struct_0(X1),X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_46, plain, (v2_compts_1(u1_struct_0(X1),X1)|~v2_compts_1(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r1_tarski(u1_struct_0(X1),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (k2_struct_0(k1_pre_topc(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.13/0.38  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (v2_compts_1(k2_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_pre_topc(esk2_0,esk3_0))|v2_compts_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_33])])).
% 0.13/0.38  cnf(c_0_50, plain, (v1_compts_1(X1)|~v2_compts_1(k2_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))|~v2_compts_1(esk3_0,X1)|~m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_42]), c_0_42]), c_0_42]), c_0_48])])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))|v2_compts_1(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_49, c_0_47])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|~v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_47]), c_0_33])])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_25]), c_0_18])]), c_0_52])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[c_0_53])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.13/0.38  cnf(c_0_58, plain, (esk1_3(X1,X2,X3)=X3|v2_compts_1(X3,X1)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (~v2_compts_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (esk1_3(esk2_0,X1,esk3_0)=esk3_0|~m1_pre_topc(X1,esk2_0)|~r1_tarski(esk3_0,k2_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_17]), c_0_18])]), c_0_59])).
% 0.13/0.38  cnf(c_0_61, plain, (v2_compts_1(X3,X1)|~v2_compts_1(esk1_3(X1,X2,X3),X2)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (esk1_3(esk2_0,k1_pre_topc(esk2_0,esk3_0),esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_47]), c_0_25]), c_0_48])])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_55]), c_0_25]), c_0_18]), c_0_17]), c_0_47]), c_0_48])]), c_0_59]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 64
% 0.13/0.38  # Proof object clause steps            : 39
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 24
% 0.13/0.38  # Proof object clause conjectures      : 21
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 18
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 13
% 0.13/0.38  # Proof object simplifying inferences  : 44
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 32
% 0.13/0.38  # Removed in clause preprocessing      : 4
% 0.13/0.38  # Initial clauses in saturation        : 28
% 0.13/0.38  # Processed clauses                    : 128
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 7
% 0.13/0.38  # ...remaining for further processing  : 119
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 10
% 0.13/0.38  # Generated clauses                    : 179
% 0.13/0.38  # ...of the previous two non-trivial   : 174
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 176
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 83
% 0.13/0.38  #    Positive orientable unit clauses  : 43
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 39
% 0.13/0.38  # Current number of unprocessed clauses: 91
% 0.13/0.38  # ...number of literals in the above   : 388
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 34
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 495
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 195
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 9
% 0.13/0.38  # Unit Clause-clause subsumption calls : 25
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 33
% 0.13/0.38  # BW rewrite match successes           : 4
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 7140
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.036 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.040 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
