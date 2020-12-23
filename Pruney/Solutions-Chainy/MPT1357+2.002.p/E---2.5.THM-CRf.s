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
% DateTime   : Thu Dec  3 11:14:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 498 expanded)
%              Number of clauses        :   45 ( 203 expanded)
%              Number of leaves         :   10 ( 121 expanded)
%              Depth                    :   11
%              Number of atoms          :  296 (4336 expanded)
%              Number of equality atoms :   38 ( 752 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   40 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t10_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_compts_1(X1)
      <=> v2_compts_1(k2_struct_0(X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | u1_struct_0(k1_pre_topc(X16,X17)) = X17 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_12,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X9,X10,X11] :
      ( ( X11 != k1_pre_topc(X9,X10)
        | k2_struct_0(X11) = X10
        | ~ v1_pre_topc(X11)
        | ~ m1_pre_topc(X11,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( k2_struct_0(X11) != X10
        | X11 = k1_pre_topc(X9,X10)
        | ~ v1_pre_topc(X11)
        | ~ m1_pre_topc(X11,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_15,plain,(
    ! [X12,X13] :
      ( ( v1_pre_topc(k1_pre_topc(X12,X13))
        | ~ l1_pre_topc(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( m1_pre_topc(k1_pre_topc(X12,X13),X12)
        | ~ l1_pre_topc(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_16,plain,(
    ! [X18,X19,X20] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_17,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ v2_compts_1(X24,X22)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | X25 != X24
        | v2_compts_1(X25,X23)
        | ~ r1_tarski(X24,k2_struct_0(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk1_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X23)))
        | v2_compts_1(X24,X22)
        | ~ r1_tarski(X24,k2_struct_0(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) )
      & ( esk1_3(X22,X23,X24) = X24
        | v2_compts_1(X24,X22)
        | ~ r1_tarski(X24,k2_struct_0(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ v2_compts_1(esk1_3(X22,X23,X24),X23)
        | v2_compts_1(X24,X22)
        | ~ r1_tarski(X24,k2_struct_0(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).

cnf(c_0_23,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk2_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X14)
      | l1_pre_topc(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_31,plain,
    ( v2_compts_1(X3,X1)
    | ~ v2_compts_1(esk1_3(X1,X2,X3),X2)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( esk1_3(X1,X2,X3) = X3
    | v2_compts_1(X3,X1)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_36,plain,(
    ! [X21] :
      ( ( ~ v1_compts_1(X21)
        | v2_compts_1(k2_struct_0(X21),X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ v2_compts_1(k2_struct_0(X21),X21)
        | v1_compts_1(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_compts_1])])])).

cnf(c_0_37,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_19])])).

cnf(c_0_39,plain,
    ( v2_compts_1(X3,X4)
    | ~ v2_compts_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | X3 != X1
    | ~ r1_tarski(X1,k2_struct_0(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( v2_compts_1(k2_struct_0(X1),X2)
    | ~ v2_compts_1(esk1_3(X2,X1,k2_struct_0(X1)),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk2_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_19])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( esk1_3(X1,X2,k2_struct_0(X2)) = k2_struct_0(X2)
    | v2_compts_1(k2_struct_0(X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_44,plain,
    ( v2_compts_1(k2_struct_0(X1),X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_19])])).

cnf(c_0_46,negated_conjecture,
    ( v2_compts_1(esk3_0,esk2_0)
    | v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
    | v2_compts_1(esk3_0,esk2_0)
    | v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,plain,
    ( v2_compts_1(X1,X2)
    | ~ v2_compts_1(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_26])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( v2_compts_1(esk3_0,X1)
    | ~ v2_compts_1(esk1_3(X1,k1_pre_topc(esk2_0,esk3_0),esk3_0),k1_pre_topc(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( esk1_3(X1,k1_pre_topc(esk2_0,esk3_0),esk3_0) = esk3_0
    | v2_compts_1(esk3_0,X1)
    | ~ m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))
    | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_41]),c_0_45])])).

cnf(c_0_52,negated_conjecture,
    ( v2_compts_1(esk3_0,esk2_0)
    | v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( v2_compts_1(X1,k1_pre_topc(esk2_0,esk3_0))
    | ~ v2_compts_1(X1,X2)
    | ~ m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_41]),c_0_27]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( v2_compts_1(esk3_0,esk2_0)
    | ~ v2_compts_1(esk1_3(esk2_0,k1_pre_topc(esk2_0,esk3_0),esk3_0),k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_19])])).

cnf(c_0_55,negated_conjecture,
    ( esk1_3(esk2_0,k1_pre_topc(esk2_0,esk3_0),esk3_0) = esk3_0
    | v2_compts_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_38]),c_0_19])])).

cnf(c_0_56,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))
    | v2_compts_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,esk2_0)
    | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
    | ~ v2_compts_1(esk3_0,esk2_0)
    | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_58,plain,
    ( v1_compts_1(X1)
    | ~ v2_compts_1(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))
    | ~ v2_compts_1(esk3_0,X1)
    | ~ m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_34])).

cnf(c_0_60,negated_conjecture,
    ( v2_compts_1(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,esk2_0)
    | ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( v1_compts_1(k1_pre_topc(esk2_0,esk3_0))
    | ~ v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_45])])).

cnf(c_0_63,negated_conjecture,
    ( v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_38]),c_0_19])])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_compts_1(k1_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_60])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:17:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.46  # and selection function SelectNewComplexAHPNS.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.029 s
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(t12_compts_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((X2=k1_xboole_0=>(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2))))&(v2_pre_topc(X1)=>(X2=k1_xboole_0|(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_compts_1)).
% 0.19/0.46  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.19/0.46  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.46  fof(d10_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((v1_pre_topc(X3)&m1_pre_topc(X3,X1))=>(X3=k1_pre_topc(X1,X2)<=>k2_struct_0(X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 0.19/0.46  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.19/0.46  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.19/0.46  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.46  fof(t11_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,k2_struct_0(X2))=>(v2_compts_1(X3,X1)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X4=X3=>v2_compts_1(X4,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_compts_1)).
% 0.19/0.46  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.46  fof(t10_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_compts_1(X1)<=>v2_compts_1(k2_struct_0(X1),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_compts_1)).
% 0.19/0.46  fof(c_0_10, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((X2=k1_xboole_0=>(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2))))&(v2_pre_topc(X1)=>(X2=k1_xboole_0|(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2))))))))), inference(assume_negation,[status(cth)],[t12_compts_1])).
% 0.19/0.46  fof(c_0_11, plain, ![X16, X17]:(~l1_pre_topc(X16)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|u1_struct_0(k1_pre_topc(X16,X17))=X17)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.19/0.46  fof(c_0_12, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((v2_pre_topc(esk2_0)|esk3_0=k1_xboole_0)&((esk3_0!=k1_xboole_0|esk3_0=k1_xboole_0)&((~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|esk3_0=k1_xboole_0)&(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|esk3_0=k1_xboole_0))))&(((v2_pre_topc(esk2_0)|(~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&((esk3_0!=k1_xboole_0|(~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&((~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|(~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|(~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0)))))))&((v2_pre_topc(esk2_0)|(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&((esk3_0!=k1_xboole_0|(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&((~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))&(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|(v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.19/0.46  fof(c_0_13, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.46  fof(c_0_14, plain, ![X9, X10, X11]:((X11!=k1_pre_topc(X9,X10)|k2_struct_0(X11)=X10|(~v1_pre_topc(X11)|~m1_pre_topc(X11,X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))&(k2_struct_0(X11)!=X10|X11=k1_pre_topc(X9,X10)|(~v1_pre_topc(X11)|~m1_pre_topc(X11,X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).
% 0.19/0.46  fof(c_0_15, plain, ![X12, X13]:((v1_pre_topc(k1_pre_topc(X12,X13))|(~l1_pre_topc(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))&(m1_pre_topc(k1_pre_topc(X12,X13),X12)|(~l1_pre_topc(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.19/0.46  fof(c_0_16, plain, ![X18, X19, X20]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,X18)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.19/0.46  cnf(c_0_17, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.46  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  fof(c_0_20, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.46  cnf(c_0_21, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.46  fof(c_0_22, plain, ![X22, X23, X24, X25]:((~v2_compts_1(X24,X22)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(X25!=X24|v2_compts_1(X25,X23)))|~r1_tarski(X24,k2_struct_0(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|~m1_pre_topc(X23,X22)|~l1_pre_topc(X22))&((m1_subset_1(esk1_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X23)))|v2_compts_1(X24,X22)|~r1_tarski(X24,k2_struct_0(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|~m1_pre_topc(X23,X22)|~l1_pre_topc(X22))&((esk1_3(X22,X23,X24)=X24|v2_compts_1(X24,X22)|~r1_tarski(X24,k2_struct_0(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|~m1_pre_topc(X23,X22)|~l1_pre_topc(X22))&(~v2_compts_1(esk1_3(X22,X23,X24),X23)|v2_compts_1(X24,X22)|~r1_tarski(X24,k2_struct_0(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|~m1_pre_topc(X23,X22)|~l1_pre_topc(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).
% 0.19/0.46  cnf(c_0_23, plain, (k2_struct_0(X1)=X3|X1!=k1_pre_topc(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.46  cnf(c_0_24, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_25, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_26, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.46  cnf(c_0_27, negated_conjecture, (u1_struct_0(k1_pre_topc(esk2_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.19/0.46  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.46  cnf(c_0_29, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.46  fof(c_0_30, plain, ![X14, X15]:(~l1_pre_topc(X14)|(~m1_pre_topc(X15,X14)|l1_pre_topc(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.46  cnf(c_0_31, plain, (v2_compts_1(X3,X1)|~v2_compts_1(esk1_3(X1,X2,X3),X2)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.46  cnf(c_0_32, plain, (k2_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]), c_0_24]), c_0_25])).
% 0.19/0.46  cnf(c_0_33, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.46  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.46  cnf(c_0_35, plain, (esk1_3(X1,X2,X3)=X3|v2_compts_1(X3,X1)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.46  fof(c_0_36, plain, ![X21]:((~v1_compts_1(X21)|v2_compts_1(k2_struct_0(X21),X21)|~l1_pre_topc(X21))&(~v2_compts_1(k2_struct_0(X21),X21)|v1_compts_1(X21)|~l1_pre_topc(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_compts_1])])])).
% 0.19/0.46  cnf(c_0_37, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.46  cnf(c_0_38, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_18]), c_0_19])])).
% 0.19/0.46  cnf(c_0_39, plain, (v2_compts_1(X3,X4)|~v2_compts_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|X3!=X1|~r1_tarski(X1,k2_struct_0(X4))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X4,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.46  cnf(c_0_40, plain, (v2_compts_1(k2_struct_0(X1),X2)|~v2_compts_1(esk1_3(X2,X1,k2_struct_0(X1)),X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.19/0.46  cnf(c_0_41, negated_conjecture, (k2_struct_0(k1_pre_topc(esk2_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_18]), c_0_19])])).
% 0.19/0.46  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.46  cnf(c_0_43, plain, (esk1_3(X1,X2,k2_struct_0(X2))=k2_struct_0(X2)|v2_compts_1(k2_struct_0(X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_35, c_0_29])).
% 0.19/0.46  cnf(c_0_44, plain, (v2_compts_1(k2_struct_0(X1),X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.46  cnf(c_0_45, negated_conjecture, (l1_pre_topc(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_19])])).
% 0.19/0.46  cnf(c_0_46, negated_conjecture, (v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  cnf(c_0_47, plain, (v2_compts_1(X1,X2)|~v2_compts_1(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]), c_0_26])).
% 0.19/0.46  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.46  cnf(c_0_49, negated_conjecture, (v2_compts_1(esk3_0,X1)|~v2_compts_1(esk1_3(X1,k1_pre_topc(esk2_0,esk3_0),esk3_0),k1_pre_topc(esk2_0,esk3_0))|~m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.19/0.46  cnf(c_0_50, negated_conjecture, (esk1_3(X1,k1_pre_topc(esk2_0,esk3_0),esk3_0)=esk3_0|v2_compts_1(esk3_0,X1)|~m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_41]), c_0_42])).
% 0.19/0.46  cnf(c_0_51, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_41]), c_0_45])])).
% 0.19/0.46  cnf(c_0_52, negated_conjecture, (v2_compts_1(esk3_0,esk2_0)|v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[c_0_46])).
% 0.19/0.46  cnf(c_0_53, negated_conjecture, (v2_compts_1(X1,k1_pre_topc(esk2_0,esk3_0))|~v2_compts_1(X1,X2)|~m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_41]), c_0_27]), c_0_48])).
% 0.19/0.46  cnf(c_0_54, negated_conjecture, (v2_compts_1(esk3_0,esk2_0)|~v2_compts_1(esk1_3(esk2_0,k1_pre_topc(esk2_0,esk3_0),esk3_0),k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_38]), c_0_19])])).
% 0.19/0.46  cnf(c_0_55, negated_conjecture, (esk1_3(esk2_0,k1_pre_topc(esk2_0,esk3_0),esk3_0)=esk3_0|v2_compts_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_38]), c_0_19])])).
% 0.19/0.46  cnf(c_0_56, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))|v2_compts_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.46  cnf(c_0_57, negated_conjecture, (~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  cnf(c_0_58, plain, (v1_compts_1(X1)|~v2_compts_1(k2_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.46  cnf(c_0_59, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))|~v2_compts_1(esk3_0,X1)|~m1_pre_topc(k1_pre_topc(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_53, c_0_34])).
% 0.19/0.46  cnf(c_0_60, negated_conjecture, (v2_compts_1(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.19/0.46  cnf(c_0_61, negated_conjecture, (~v2_compts_1(esk3_0,esk2_0)|~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[c_0_57])).
% 0.19/0.46  cnf(c_0_62, negated_conjecture, (v1_compts_1(k1_pre_topc(esk2_0,esk3_0))|~v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_41]), c_0_45])])).
% 0.19/0.46  cnf(c_0_63, negated_conjecture, (v2_compts_1(esk3_0,k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_38]), c_0_19])])).
% 0.19/0.46  cnf(c_0_64, negated_conjecture, (~v1_compts_1(k1_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_60])])).
% 0.19/0.46  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])]), c_0_64]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 66
% 0.19/0.46  # Proof object clause steps            : 45
% 0.19/0.46  # Proof object formula steps           : 21
% 0.19/0.46  # Proof object conjectures             : 28
% 0.19/0.46  # Proof object clause conjectures      : 25
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 18
% 0.19/0.46  # Proof object initial formulas used   : 10
% 0.19/0.46  # Proof object generating inferences   : 20
% 0.19/0.46  # Proof object simplifying inferences  : 37
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 10
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 32
% 0.19/0.46  # Removed in clause preprocessing      : 3
% 0.19/0.46  # Initial clauses in saturation        : 29
% 0.19/0.46  # Processed clauses                    : 587
% 0.19/0.46  # ...of these trivial                  : 38
% 0.19/0.46  # ...subsumed                          : 85
% 0.19/0.46  # ...remaining for further processing  : 464
% 0.19/0.46  # Other redundant clauses eliminated   : 5
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 3
% 0.19/0.46  # Backward-rewritten                   : 57
% 0.19/0.46  # Generated clauses                    : 1812
% 0.19/0.46  # ...of the previous two non-trivial   : 1654
% 0.19/0.46  # Contextual simplify-reflections      : 22
% 0.19/0.46  # Paramodulations                      : 1807
% 0.19/0.46  # Factorizations                       : 0
% 0.19/0.46  # Equation resolutions                 : 5
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 399
% 0.19/0.46  #    Positive orientable unit clauses  : 135
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 1
% 0.19/0.46  #    Non-unit-clauses                  : 263
% 0.19/0.46  # Current number of unprocessed clauses: 1093
% 0.19/0.46  # ...number of literals in the above   : 3728
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 60
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 9387
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 6151
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 110
% 0.19/0.46  # Unit Clause-clause subsumption calls : 1436
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 1757
% 0.19/0.46  # BW rewrite match successes           : 14
% 0.19/0.46  # Condensation attempts                : 587
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 110217
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.118 s
% 0.19/0.47  # System time              : 0.003 s
% 0.19/0.47  # Total time               : 0.121 s
% 0.19/0.47  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
