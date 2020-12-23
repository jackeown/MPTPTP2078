%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_1__t90_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:33 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  96 expanded)
%              Number of clauses        :   24 (  33 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  154 ( 458 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t90_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_tops_1(X2,X1)
                  & v3_tops_1(X3,X1) )
               => v3_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',t90_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',redefinition_k4_subset_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',commutativity_k2_xboole_0)).

fof(t85_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v2_tops_1(X2,X1)
                  & v2_tops_1(X3,X1)
                  & v4_pre_topc(X3,X1) )
               => v2_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',t85_tops_1)).

fof(t50_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => k2_pre_topc(X1,k4_subset_1(u1_struct_0(X1),X2,X3)) = k4_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',t50_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',dt_k2_pre_topc)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',fc1_tops_1)).

fof(d5_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
          <=> v2_tops_1(k2_pre_topc(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',d5_tops_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t90_tops_1.p',dt_k4_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v3_tops_1(X2,X1)
                    & v3_tops_1(X3,X1) )
                 => v3_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t90_tops_1])).

fof(c_0_10,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v3_tops_1(esk2_0,esk1_0)
    & v3_tops_1(esk3_0,esk1_0)
    & ~ v3_tops_1(k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | ~ m1_subset_1(X34,k1_zfmisc_1(X32))
      | k4_subset_1(X32,X33,X34) = k2_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_12,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_13,plain,(
    ! [X54,X55,X56] :
      ( ~ v2_pre_topc(X54)
      | ~ l1_pre_topc(X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
      | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54)))
      | ~ v2_tops_1(X55,X54)
      | ~ v2_tops_1(X56,X54)
      | ~ v4_pre_topc(X56,X54)
      | v2_tops_1(k4_subset_1(u1_struct_0(X54),X55,X56),X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_tops_1])])])).

fof(c_0_14,plain,(
    ! [X45,X46,X47] :
      ( ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
      | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
      | k2_pre_topc(X45,k4_subset_1(u1_struct_0(X45),X46,X47)) = k4_subset_1(u1_struct_0(X45),k2_pre_topc(X45,X46),k2_pre_topc(X45,X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_pre_topc])])])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | m1_subset_1(k2_pre_topc(X16,X17),k1_zfmisc_1(u1_struct_0(X16))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_16,plain,(
    ! [X59,X60] :
      ( ~ v2_pre_topc(X59)
      | ~ l1_pre_topc(X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))
      | v4_pre_topc(k2_pre_topc(X59,X60),X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_17,negated_conjecture,
    ( ~ v3_tops_1(k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X14,X15] :
      ( ( ~ v3_tops_1(X15,X14)
        | v2_tops_1(k2_pre_topc(X14,X15),X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( ~ v2_tops_1(k2_pre_topc(X14,X15),X14)
        | v3_tops_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).

cnf(c_0_23,plain,
    ( v2_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tops_1(X2,X1)
    | ~ v2_tops_1(X3,X1)
    | ~ v4_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k2_pre_topc(X1,k4_subset_1(u1_struct_0(X1),X2,X3)) = k4_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_27,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
      | m1_subset_1(k4_subset_1(X18,X19,X20),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_28,negated_conjecture,
    ( ~ v3_tops_1(k2_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_29,plain,
    ( k4_subset_1(X1,X2,X3) = k2_xboole_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_30,plain,
    ( v3_tops_1(X2,X1)
    | ~ v2_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v2_tops_1(k2_pre_topc(X1,k4_subset_1(u1_struct_0(X1),X2,X3)),X1)
    | ~ v2_tops_1(k2_pre_topc(X1,X3),X1)
    | ~ v2_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_25]),c_0_26])).

cnf(c_0_32,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( ~ v3_tops_1(k4_subset_1(X1,esk3_0,esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( v3_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_tops_1(k2_pre_topc(X1,X3),X1)
    | ~ v2_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ v2_tops_1(k2_pre_topc(esk1_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_20]),c_0_19]),c_0_35]),c_0_36])])).

cnf(c_0_38,plain,
    ( v2_tops_1(k2_pre_topc(X2,X1),X2)
    | ~ v3_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( v3_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_19]),c_0_35])])).

cnf(c_0_41,negated_conjecture,
    ( v3_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_38]),c_0_41]),c_0_20]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
