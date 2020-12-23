%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1124+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:02 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   44 (  93 expanded)
%              Number of clauses        :   25 (  37 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 385 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_pre_topc,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t3_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t4_subset)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',d2_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t55_pre_topc])).

fof(c_0_10,plain,(
    ! [X262,X263] :
      ( ~ l1_pre_topc(X262)
      | ~ m1_pre_topc(X263,X262)
      | l1_pre_topc(X263) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ~ m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X295] :
      ( ~ l1_pre_topc(X295)
      | l1_struct_0(X295) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_13,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X252,X253,X254,X256,X258] :
      ( ( r1_tarski(k2_struct_0(X253),k2_struct_0(X252))
        | ~ m1_pre_topc(X253,X252)
        | ~ l1_pre_topc(X253)
        | ~ l1_pre_topc(X252) )
      & ( m1_subset_1(esk26_3(X252,X253,X254),k1_zfmisc_1(u1_struct_0(X252)))
        | ~ r2_hidden(X254,u1_pre_topc(X253))
        | ~ m1_subset_1(X254,k1_zfmisc_1(u1_struct_0(X253)))
        | ~ m1_pre_topc(X253,X252)
        | ~ l1_pre_topc(X253)
        | ~ l1_pre_topc(X252) )
      & ( r2_hidden(esk26_3(X252,X253,X254),u1_pre_topc(X252))
        | ~ r2_hidden(X254,u1_pre_topc(X253))
        | ~ m1_subset_1(X254,k1_zfmisc_1(u1_struct_0(X253)))
        | ~ m1_pre_topc(X253,X252)
        | ~ l1_pre_topc(X253)
        | ~ l1_pre_topc(X252) )
      & ( X254 = k9_subset_1(u1_struct_0(X253),esk26_3(X252,X253,X254),k2_struct_0(X253))
        | ~ r2_hidden(X254,u1_pre_topc(X253))
        | ~ m1_subset_1(X254,k1_zfmisc_1(u1_struct_0(X253)))
        | ~ m1_pre_topc(X253,X252)
        | ~ l1_pre_topc(X253)
        | ~ l1_pre_topc(X252) )
      & ( ~ m1_subset_1(X256,k1_zfmisc_1(u1_struct_0(X252)))
        | ~ r2_hidden(X256,u1_pre_topc(X252))
        | X254 != k9_subset_1(u1_struct_0(X253),X256,k2_struct_0(X253))
        | r2_hidden(X254,u1_pre_topc(X253))
        | ~ m1_subset_1(X254,k1_zfmisc_1(u1_struct_0(X253)))
        | ~ m1_pre_topc(X253,X252)
        | ~ l1_pre_topc(X253)
        | ~ l1_pre_topc(X252) )
      & ( m1_subset_1(esk27_2(X252,X253),k1_zfmisc_1(u1_struct_0(X253)))
        | ~ r1_tarski(k2_struct_0(X253),k2_struct_0(X252))
        | m1_pre_topc(X253,X252)
        | ~ l1_pre_topc(X253)
        | ~ l1_pre_topc(X252) )
      & ( ~ r2_hidden(esk27_2(X252,X253),u1_pre_topc(X253))
        | ~ m1_subset_1(X258,k1_zfmisc_1(u1_struct_0(X252)))
        | ~ r2_hidden(X258,u1_pre_topc(X252))
        | esk27_2(X252,X253) != k9_subset_1(u1_struct_0(X253),X258,k2_struct_0(X253))
        | ~ r1_tarski(k2_struct_0(X253),k2_struct_0(X252))
        | m1_pre_topc(X253,X252)
        | ~ l1_pre_topc(X253)
        | ~ l1_pre_topc(X252) )
      & ( m1_subset_1(esk28_2(X252,X253),k1_zfmisc_1(u1_struct_0(X252)))
        | r2_hidden(esk27_2(X252,X253),u1_pre_topc(X253))
        | ~ r1_tarski(k2_struct_0(X253),k2_struct_0(X252))
        | m1_pre_topc(X253,X252)
        | ~ l1_pre_topc(X253)
        | ~ l1_pre_topc(X252) )
      & ( r2_hidden(esk28_2(X252,X253),u1_pre_topc(X252))
        | r2_hidden(esk27_2(X252,X253),u1_pre_topc(X253))
        | ~ r1_tarski(k2_struct_0(X253),k2_struct_0(X252))
        | m1_pre_topc(X253,X252)
        | ~ l1_pre_topc(X253)
        | ~ l1_pre_topc(X252) )
      & ( esk27_2(X252,X253) = k9_subset_1(u1_struct_0(X253),esk28_2(X252,X253),k2_struct_0(X253))
        | r2_hidden(esk27_2(X252,X253),u1_pre_topc(X253))
        | ~ r1_tarski(k2_struct_0(X253),k2_struct_0(X252))
        | m1_pre_topc(X253,X252)
        | ~ l1_pre_topc(X253)
        | ~ l1_pre_topc(X252) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_17,plain,(
    ! [X184] :
      ( ~ l1_struct_0(X184)
      | k2_struct_0(X184) = u1_struct_0(X184) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_18,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_20,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

fof(c_0_24,plain,(
    ! [X73,X74] :
      ( ( ~ m1_subset_1(X73,k1_zfmisc_1(X74))
        | r1_tarski(X73,X74) )
      & ( ~ r1_tarski(X73,X74)
        | m1_subset_1(X73,k1_zfmisc_1(X74)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

fof(c_0_28,plain,(
    ! [X189] :
      ( v2_struct_0(X189)
      | ~ l1_struct_0(X189)
      | ~ v1_xboole_0(u1_struct_0(X189)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_29,plain,(
    ! [X79,X80,X81] :
      ( ~ r2_hidden(X79,X80)
      | ~ m1_subset_1(X80,k1_zfmisc_1(X81))
      | m1_subset_1(X79,X81) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_26]),c_0_27]),c_0_15])])).

fof(c_0_32,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X25,X24)
        | r2_hidden(X25,X24)
        | v1_xboole_0(X24) )
      & ( ~ r2_hidden(X25,X24)
        | m1_subset_1(X25,X24)
        | v1_xboole_0(X24) )
      & ( ~ m1_subset_1(X25,X24)
        | v1_xboole_0(X25)
        | ~ v1_xboole_0(X24) )
      & ( ~ v1_xboole_0(X25)
        | m1_subset_1(X25,X24)
        | ~ v1_xboole_0(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
