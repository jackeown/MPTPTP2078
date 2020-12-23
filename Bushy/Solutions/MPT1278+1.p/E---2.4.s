%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_1__t97_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:35 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   30 (  81 expanded)
%              Number of clauses        :   17 (  28 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  107 ( 344 expanded)
%              Number of equality atoms :   12 (  56 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t97_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
              & v3_tops_1(X2,X1) )
           => X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t97_tops_1.p',t97_tops_1)).

fof(t80_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( X3 != k1_xboole_0
                    & v3_pre_topc(X3,X1)
                    & r1_xboole_0(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t97_tops_1.p',t80_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t97_tops_1.p',dt_k3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t97_tops_1.p',d5_subset_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t97_tops_1.p',t79_xboole_1)).

fof(fc15_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v3_tops_1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t97_tops_1.p',fc15_tops_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ( v3_pre_topc(X2,X1)
                & v3_tops_1(X2,X1) )
             => X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t97_tops_1])).

fof(c_0_7,plain,(
    ! [X40,X41,X42] :
      ( ( ~ v1_tops_1(X41,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))
        | X42 = k1_xboole_0
        | ~ v3_pre_topc(X42,X40)
        | ~ r1_xboole_0(X41,X42)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( m1_subset_1(esk6_2(X40,X41),k1_zfmisc_1(u1_struct_0(X40)))
        | v1_tops_1(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( esk6_2(X40,X41) != k1_xboole_0
        | v1_tops_1(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v3_pre_topc(esk6_2(X40,X41),X40)
        | v1_tops_1(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( r1_xboole_0(X41,esk6_2(X40,X41))
        | v1_tops_1(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_tops_1])])])])])).

fof(c_0_8,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v3_pre_topc(esk2_0,esk1_0)
    & v3_tops_1(esk2_0,esk1_0)
    & esk2_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_10,plain,
    ( X3 = k1_xboole_0
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X3,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | k3_subset_1(X8,X9) = k4_xboole_0(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_tops_1(X1,esk1_0)
    | ~ r1_xboole_0(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

cnf(c_0_20,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X36,X37] : r1_xboole_0(k4_xboole_0(X36,X37),X37) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_22,plain,(
    ! [X46,X47] :
      ( ~ v2_pre_topc(X46)
      | ~ l1_pre_topc(X46)
      | ~ v3_tops_1(X47,X46)
      | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
      | v1_tops_1(k3_subset_1(u1_struct_0(X46),X47),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc15_tops_1])])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),esk2_0) = k4_xboole_0(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v3_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_tops_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24]),c_0_25])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_11]),c_0_27]),c_0_13]),c_0_14])]),c_0_24]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
