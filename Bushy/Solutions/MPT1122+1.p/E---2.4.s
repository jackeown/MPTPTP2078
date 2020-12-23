%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : pre_topc__t53_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:44 EDT 2019

% Result     : Theorem 151.19s
% Output     : CNFRefutation 151.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 156 expanded)
%              Number of clauses        :   30 (  62 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  166 ( 766 expanded)
%              Number of equality atoms :   31 ( 188 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
             => k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',t53_pre_topc)).

fof(d6_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',d6_pre_topc)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',t22_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',dt_l1_pre_topc)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',t52_pre_topc)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',dt_k7_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',redefinition_k7_subset_1)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',dt_k2_struct_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ( v3_pre_topc(X2,X1)
               => k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
              & ( ( v2_pre_topc(X1)
                  & k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
               => v3_pre_topc(X2,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_pre_topc])).

fof(c_0_9,plain,(
    ! [X8,X9] :
      ( ( ~ v4_pre_topc(X9,X8)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X8),k2_struct_0(X8),X9),X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X8),k2_struct_0(X8),X9),X8)
        | v4_pre_topc(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).

fof(c_0_10,plain,(
    ! [X28,X29] :
      ( ~ l1_struct_0(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | k7_subset_1(u1_struct_0(X28),k2_struct_0(X28),k7_subset_1(u1_struct_0(X28),k2_struct_0(X28),X29)) = X29 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

fof(c_0_11,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | l1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_12,plain,(
    ! [X39,X40] :
      ( ( ~ v4_pre_topc(X40,X39)
        | k2_pre_topc(X39,X40) = X40
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) )
      & ( ~ v2_pre_topc(X39)
        | k2_pre_topc(X39,X40) != X40
        | v4_pre_topc(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( v2_pre_topc(esk1_0)
      | v3_pre_topc(esk2_0,esk1_0) )
    & ( k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)
      | v3_pre_topc(esk2_0,esk1_0) )
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | v3_pre_topc(esk2_0,esk1_0) )
    & ( v2_pre_topc(esk1_0)
      | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) )
    & ( k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)
      | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) )
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_14,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v4_pre_topc(X1,esk1_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | k2_pre_topc(esk1_0,X1) != X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

fof(c_0_22,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | m1_subset_1(k7_subset_1(X13,X14,X15),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

cnf(c_0_23,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | v3_pre_topc(X1,esk1_0)
    | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),X1)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),X1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19])])).

cnf(c_0_24,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | k7_subset_1(X23,X24,X25) = k4_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_26,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | v3_pre_topc(X1,esk1_0)
    | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),X1)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_29,plain,(
    ! [X12] :
      ( ~ l1_struct_0(X12)
      | m1_subset_1(k2_struct_0(X12),k1_zfmisc_1(u1_struct_0(X12))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_30,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,plain,
    ( v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_15]),c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( k2_pre_topc(esk1_0,k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_16]),c_0_19])])).

cnf(c_0_41,plain,
    ( k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k2_pre_topc(esk1_0,k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_43,plain,
    ( k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_40]),c_0_28]),c_0_19])])).

cnf(c_0_45,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_16]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
