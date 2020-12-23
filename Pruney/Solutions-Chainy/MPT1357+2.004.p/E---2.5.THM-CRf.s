%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 503 expanded)
%              Number of clauses        :   47 ( 206 expanded)
%              Number of leaves         :   11 ( 123 expanded)
%              Depth                    :   11
%              Number of atoms          :  292 (4023 expanded)
%              Number of equality atoms :   32 ( 710 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(t10_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_compts_1(X1)
      <=> v2_compts_1(k2_struct_0(X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

fof(c_0_11,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | k2_struct_0(X9) = u1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_13,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_14,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
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

cnf(c_0_18,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | l1_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_21,plain,(
    ! [X17,X18,X19] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X10,X11] :
      ( ( v1_pre_topc(k1_pre_topc(X10,X11))
        | ~ l1_pre_topc(X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10))) )
      & ( m1_pre_topc(k1_pre_topc(X10,X11),X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_25,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])).

cnf(c_0_26,plain,
    ( v2_compts_1(X3,X1)
    | ~ v2_compts_1(esk1_3(X1,X2,X3),X2)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_31,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | u1_struct_0(k1_pre_topc(X15,X16)) = X16 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_32,plain,(
    ! [X20] :
      ( ( ~ v1_compts_1(X20)
        | v2_compts_1(k2_struct_0(X20),X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ v2_compts_1(k2_struct_0(X20),X20)
        | v1_compts_1(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_compts_1])])])).

cnf(c_0_33,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( v2_compts_1(X3,X4)
    | ~ v2_compts_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | X3 != X1
    | ~ r1_tarski(X1,k2_struct_0(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( v2_compts_1(X1,X2)
    | ~ v2_compts_1(esk1_3(X2,X3,X1),X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_38,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( esk1_3(X1,X2,X3) = X3
    | v2_compts_1(X3,X1)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,plain,
    ( v2_compts_1(k2_struct_0(X1),X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_43,plain,
    ( v2_compts_1(X1,X2)
    | ~ v2_compts_1(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_29])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,plain,
    ( v2_compts_1(u1_struct_0(X1),X2)
    | ~ v2_compts_1(esk1_3(X2,X1,u1_struct_0(X1)),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_23]),c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk2_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_35])])).

cnf(c_0_47,plain,
    ( esk1_3(X1,X2,X3) = X3
    | v2_compts_1(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_27]),c_0_28])).

cnf(c_0_48,plain,
    ( v2_compts_1(u1_struct_0(X1),X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_42]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( v2_compts_1(esk3_0,esk2_0)
    | v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
    | v2_compts_1(esk3_0,esk2_0)
    | v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_51,plain,
    ( v2_compts_1(X1,X2)
    | ~ v2_compts_1(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_27]),c_0_44]),c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( v2_compts_1(esk3_0,X1)
    | ~ v2_compts_1(esk1_3(X1,k1_pre_topc(esk2_0,esk3_0),esk3_0),k1_pre_topc(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( esk1_3(X1,X2,u1_struct_0(X2)) = u1_struct_0(X2)
    | v2_compts_1(u1_struct_0(X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_23]),c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))
    | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_46]),c_0_49])])).

cnf(c_0_55,negated_conjecture,
    ( v2_compts_1(esk3_0,esk2_0)
    | v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( v1_compts_1(X1)
    | ~ v2_compts_1(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( v2_compts_1(X1,k1_pre_topc(esk2_0,esk3_0))
    | ~ v2_compts_1(X1,X2)
    | ~ m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( v2_compts_1(esk3_0,esk2_0)
    | ~ v2_compts_1(esk1_3(esk2_0,k1_pre_topc(esk2_0,esk3_0),esk3_0),k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_42]),c_0_35])])).

cnf(c_0_59,negated_conjecture,
    ( esk1_3(esk2_0,k1_pre_topc(esk2_0,esk3_0),esk3_0) = esk3_0
    | v2_compts_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_42]),c_0_46]),c_0_46]),c_0_46]),c_0_35])])).

cnf(c_0_60,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))
    | v2_compts_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,esk2_0)
    | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
    | ~ v2_compts_1(esk3_0,esk2_0)
    | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_62,plain,
    ( v1_compts_1(X1)
    | ~ v2_compts_1(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_27])).

cnf(c_0_63,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))
    | ~ v2_compts_1(esk3_0,X1)
    | ~ m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( v2_compts_1(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,esk2_0)
    | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
    | ~ v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_46]),c_0_49])])).

cnf(c_0_67,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_42]),c_0_35])])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_64])])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:16:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.51  # and selection function SelectNewComplexAHPNS.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.028 s
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.51  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.51  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.51  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.51  fof(t12_compts_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((X2=k1_xboole_0=>(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2))))&(v2_pre_topc(X1)=>(X2=k1_xboole_0|(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_compts_1)).
% 0.19/0.51  fof(t11_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,k2_struct_0(X2))=>(v2_compts_1(X3,X1)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X4=X3=>v2_compts_1(X4,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_compts_1)).
% 0.19/0.51  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.51  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.19/0.51  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.19/0.51  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.19/0.51  fof(t10_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_compts_1(X1)<=>v2_compts_1(k2_struct_0(X1),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_compts_1)).
% 0.19/0.51  fof(c_0_11, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.51  fof(c_0_12, plain, ![X9]:(~l1_struct_0(X9)|k2_struct_0(X9)=u1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.51  fof(c_0_13, plain, ![X12]:(~l1_pre_topc(X12)|l1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.51  fof(c_0_14, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.51  cnf(c_0_15, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  fof(c_0_16, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((X2=k1_xboole_0=>(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2))))&(v2_pre_topc(X1)=>(X2=k1_xboole_0|(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2))))))))), inference(assume_negation,[status(cth)],[t12_compts_1])).
% 0.19/0.51  fof(c_0_17, plain, ![X21, X22, X23, X24]:((~v2_compts_1(X23,X21)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(X24!=X23|v2_compts_1(X24,X22)))|~r1_tarski(X23,k2_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X21))&((m1_subset_1(esk1_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X22)))|v2_compts_1(X23,X21)|~r1_tarski(X23,k2_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X21))&((esk1_3(X21,X22,X23)=X23|v2_compts_1(X23,X21)|~r1_tarski(X23,k2_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X21))&(~v2_compts_1(esk1_3(X21,X22,X23),X22)|v2_compts_1(X23,X21)|~r1_tarski(X23,k2_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).
% 0.19/0.51  cnf(c_0_18, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.51  cnf(c_0_19, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.51  fof(c_0_20, plain, ![X13, X14]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|l1_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.51  fof(c_0_21, plain, ![X17, X18, X19]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.19/0.51  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.51  cnf(c_0_23, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.51  fof(c_0_24, plain, ![X10, X11]:((v1_pre_topc(k1_pre_topc(X10,X11))|(~l1_pre_topc(X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))))&(m1_pre_topc(k1_pre_topc(X10,X11),X10)|(~l1_pre_topc(X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.19/0.51  fof(c_0_25, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((v2_pre_topc(esk2_0)|esk3_0=k1_xboole_0)&((esk3_0!=k1_xboole_0|esk3_0=k1_xboole_0)&((~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|esk3_0=k1_xboole_0)&(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|esk3_0=k1_xboole_0))))&(((v2_pre_topc(esk2_0)|(~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&((esk3_0!=k1_xboole_0|(~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&((~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|(~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|(~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0)))))))&((v2_pre_topc(esk2_0)|(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&((esk3_0!=k1_xboole_0|(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&((~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])).
% 0.19/0.51  cnf(c_0_26, plain, (v2_compts_1(X3,X1)|~v2_compts_1(esk1_3(X1,X2,X3),X2)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.51  cnf(c_0_27, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.51  cnf(c_0_28, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.51  cnf(c_0_29, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.51  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.51  fof(c_0_31, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|u1_struct_0(k1_pre_topc(X15,X16))=X16)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.19/0.51  fof(c_0_32, plain, ![X20]:((~v1_compts_1(X20)|v2_compts_1(k2_struct_0(X20),X20)|~l1_pre_topc(X20))&(~v2_compts_1(k2_struct_0(X20),X20)|v1_compts_1(X20)|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_compts_1])])])).
% 0.19/0.51  cnf(c_0_33, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.51  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.51  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.51  cnf(c_0_36, plain, (v2_compts_1(X3,X4)|~v2_compts_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|X3!=X1|~r1_tarski(X1,k2_struct_0(X4))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X4,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.51  cnf(c_0_37, plain, (v2_compts_1(X1,X2)|~v2_compts_1(esk1_3(X2,X3,X1),X3)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.19/0.51  cnf(c_0_38, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.51  cnf(c_0_39, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.51  cnf(c_0_40, plain, (esk1_3(X1,X2,X3)=X3|v2_compts_1(X3,X1)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.51  cnf(c_0_41, plain, (v2_compts_1(k2_struct_0(X1),X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.51  cnf(c_0_42, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.19/0.51  cnf(c_0_43, plain, (v2_compts_1(X1,X2)|~v2_compts_1(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]), c_0_29])).
% 0.19/0.51  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.51  cnf(c_0_45, plain, (v2_compts_1(u1_struct_0(X1),X2)|~v2_compts_1(esk1_3(X2,X1,u1_struct_0(X1)),X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_23]), c_0_38])).
% 0.19/0.51  cnf(c_0_46, negated_conjecture, (u1_struct_0(k1_pre_topc(esk2_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_35])])).
% 0.19/0.51  cnf(c_0_47, plain, (esk1_3(X1,X2,X3)=X3|v2_compts_1(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_27]), c_0_28])).
% 0.19/0.51  cnf(c_0_48, plain, (v2_compts_1(u1_struct_0(X1),X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_27])).
% 0.19/0.51  cnf(c_0_49, negated_conjecture, (l1_pre_topc(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_42]), c_0_35])])).
% 0.19/0.51  cnf(c_0_50, negated_conjecture, (v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.51  cnf(c_0_51, plain, (v2_compts_1(X1,X2)|~v2_compts_1(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_27]), c_0_44]), c_0_28])).
% 0.19/0.51  cnf(c_0_52, negated_conjecture, (v2_compts_1(esk3_0,X1)|~v2_compts_1(esk1_3(X1,k1_pre_topc(esk2_0,esk3_0),esk3_0),k1_pre_topc(esk2_0,esk3_0))|~m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.51  cnf(c_0_53, plain, (esk1_3(X1,X2,u1_struct_0(X2))=u1_struct_0(X2)|v2_compts_1(u1_struct_0(X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_23]), c_0_38])).
% 0.19/0.51  cnf(c_0_54, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_46]), c_0_49])])).
% 0.19/0.51  cnf(c_0_55, negated_conjecture, (v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[c_0_50])).
% 0.19/0.51  cnf(c_0_56, plain, (v1_compts_1(X1)|~v2_compts_1(k2_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.51  cnf(c_0_57, negated_conjecture, (v2_compts_1(X1,k1_pre_topc(esk2_0,esk3_0))|~v2_compts_1(X1,X2)|~m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_46])).
% 0.19/0.51  cnf(c_0_58, negated_conjecture, (v2_compts_1(esk3_0,esk2_0)|~v2_compts_1(esk1_3(esk2_0,k1_pre_topc(esk2_0,esk3_0),esk3_0),k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_42]), c_0_35])])).
% 0.19/0.51  cnf(c_0_59, negated_conjecture, (esk1_3(esk2_0,k1_pre_topc(esk2_0,esk3_0),esk3_0)=esk3_0|v2_compts_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_42]), c_0_46]), c_0_46]), c_0_46]), c_0_35])])).
% 0.19/0.51  cnf(c_0_60, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))|v2_compts_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.51  cnf(c_0_61, negated_conjecture, (~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.51  cnf(c_0_62, plain, (v1_compts_1(X1)|~v2_compts_1(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_56, c_0_27])).
% 0.19/0.51  cnf(c_0_63, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))|~v2_compts_1(esk3_0,X1)|~m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_57, c_0_30])).
% 0.19/0.51  cnf(c_0_64, negated_conjecture, (v2_compts_1(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.19/0.51  cnf(c_0_65, negated_conjecture, (~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[c_0_61])).
% 0.19/0.51  cnf(c_0_66, negated_conjecture, (v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|~v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_46]), c_0_49])])).
% 0.19/0.51  cnf(c_0_67, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_42]), c_0_35])])).
% 0.19/0.51  cnf(c_0_68, negated_conjecture, (~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_64])])).
% 0.19/0.51  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])]), c_0_68]), ['proof']).
% 0.19/0.51  # SZS output end CNFRefutation
% 0.19/0.51  # Proof object total steps             : 70
% 0.19/0.51  # Proof object clause steps            : 47
% 0.19/0.51  # Proof object formula steps           : 23
% 0.19/0.51  # Proof object conjectures             : 24
% 0.19/0.51  # Proof object clause conjectures      : 21
% 0.19/0.51  # Proof object formula conjectures     : 3
% 0.19/0.51  # Proof object initial clauses used    : 18
% 0.19/0.51  # Proof object initial formulas used   : 11
% 0.19/0.51  # Proof object generating inferences   : 23
% 0.19/0.51  # Proof object simplifying inferences  : 37
% 0.19/0.51  # Training examples: 0 positive, 0 negative
% 0.19/0.51  # Parsed axioms                        : 11
% 0.19/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.51  # Initial clauses                      : 32
% 0.19/0.51  # Removed in clause preprocessing      : 3
% 0.19/0.51  # Initial clauses in saturation        : 29
% 0.19/0.51  # Processed clauses                    : 1135
% 0.19/0.51  # ...of these trivial                  : 127
% 0.19/0.51  # ...subsumed                          : 266
% 0.19/0.51  # ...remaining for further processing  : 742
% 0.19/0.51  # Other redundant clauses eliminated   : 3
% 0.19/0.51  # Clauses deleted for lack of memory   : 0
% 0.19/0.51  # Backward-subsumed                    : 9
% 0.19/0.51  # Backward-rewritten                   : 169
% 0.19/0.51  # Generated clauses                    : 5170
% 0.19/0.51  # ...of the previous two non-trivial   : 4784
% 0.19/0.51  # Contextual simplify-reflections      : 26
% 0.19/0.51  # Paramodulations                      : 5167
% 0.19/0.51  # Factorizations                       : 0
% 0.19/0.51  # Equation resolutions                 : 3
% 0.19/0.51  # Propositional unsat checks           : 0
% 0.19/0.51  #    Propositional check models        : 0
% 0.19/0.51  #    Propositional check unsatisfiable : 0
% 0.19/0.51  #    Propositional clauses             : 0
% 0.19/0.51  #    Propositional clauses after purity: 0
% 0.19/0.51  #    Propositional unsat core size     : 0
% 0.19/0.51  #    Propositional preprocessing time  : 0.000
% 0.19/0.51  #    Propositional encoding time       : 0.000
% 0.19/0.51  #    Propositional solver time         : 0.000
% 0.19/0.51  #    Success case prop preproc time    : 0.000
% 0.19/0.51  #    Success case prop encoding time   : 0.000
% 0.19/0.51  #    Success case prop solver time     : 0.000
% 0.19/0.51  # Current number of processed clauses  : 561
% 0.19/0.51  #    Positive orientable unit clauses  : 202
% 0.19/0.51  #    Positive unorientable unit clauses: 0
% 0.19/0.51  #    Negative unit clauses             : 1
% 0.19/0.51  #    Non-unit-clauses                  : 358
% 0.19/0.51  # Current number of unprocessed clauses: 3675
% 0.19/0.51  # ...number of literals in the above   : 13519
% 0.19/0.51  # Current number of archived formulas  : 0
% 0.19/0.51  # Current number of archived clauses   : 178
% 0.19/0.51  # Clause-clause subsumption calls (NU) : 18566
% 0.19/0.51  # Rec. Clause-clause subsumption calls : 12843
% 0.19/0.51  # Non-unit clause-clause subsumptions  : 301
% 0.19/0.51  # Unit Clause-clause subsumption calls : 695
% 0.19/0.51  # Rewrite failures with RHS unbound    : 0
% 0.19/0.51  # BW rewrite match attempts            : 4945
% 0.19/0.51  # BW rewrite match successes           : 25
% 0.19/0.51  # Condensation attempts                : 1135
% 0.19/0.51  # Condensation successes               : 0
% 0.19/0.51  # Termbank termtop insertions          : 294648
% 0.19/0.51  
% 0.19/0.51  # -------------------------------------------------
% 0.19/0.51  # User time                : 0.164 s
% 0.19/0.51  # System time              : 0.015 s
% 0.19/0.51  # Total time               : 0.179 s
% 0.19/0.51  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
