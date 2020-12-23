%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : compts_1__t14_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:49 EDT 2019

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   71 (10547 expanded)
%              Number of clauses        :   58 (3510 expanded)
%              Number of leaves         :    6 (2572 expanded)
%              Depth                    :   21
%              Number of atoms          :  312 (168575 expanded)
%              Number of equality atoms :   91 (49367 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   47 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_compts_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_compts_1(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( X2 != k1_xboole_0
                & v2_tops_2(X2,X1)
                & k6_setfam_1(u1_struct_0(X1),X2) = k1_xboole_0
                & ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ~ ( X3 != k1_xboole_0
                        & r1_tarski(X3,X2)
                        & v1_finset_1(X3)
                        & k6_setfam_1(u1_struct_0(X1),X3) = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t14_compts_1.p',t14_compts_1)).

fof(t13_compts_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_compts_1(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( v3_finset_1(X2)
                & v2_tops_2(X2,X1)
                & k6_setfam_1(u1_struct_0(X1),X2) = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t14_compts_1.p',t13_compts_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t14_compts_1.p',redefinition_k6_setfam_1)).

fof(d3_finset_1,axiom,(
    ! [X1] :
      ( v3_finset_1(X1)
    <=> ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( X2 != k1_xboole_0
              & r1_tarski(X2,X1)
              & v1_finset_1(X2)
              & k1_setfam_1(X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t14_compts_1.p',d3_finset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t14_compts_1.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t14_compts_1.p',t1_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ( v1_compts_1(X1)
        <=> ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ~ ( X2 != k1_xboole_0
                  & v2_tops_2(X2,X1)
                  & k6_setfam_1(u1_struct_0(X1),X2) = k1_xboole_0
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                     => ~ ( X3 != k1_xboole_0
                          & r1_tarski(X3,X2)
                          & v1_finset_1(X3)
                          & k6_setfam_1(u1_struct_0(X1),X3) = k1_xboole_0 ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t14_compts_1])).

fof(c_0_7,plain,(
    ! [X24,X25] :
      ( ( ~ v1_compts_1(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))
        | ~ v3_finset_1(X25)
        | ~ v2_tops_2(X25,X24)
        | k6_setfam_1(u1_struct_0(X24),X25) != k1_xboole_0
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk8_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))
        | v1_compts_1(X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( v3_finset_1(esk8_1(X24))
        | v1_compts_1(X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( v2_tops_2(esk8_1(X24),X24)
        | v1_compts_1(X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( k6_setfam_1(u1_struct_0(X24),esk8_1(X24)) = k1_xboole_0
        | v1_compts_1(X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_compts_1])])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X6,X7] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
        | ~ v1_compts_1(esk1_0) )
      & ( esk2_0 != k1_xboole_0
        | ~ v1_compts_1(esk1_0) )
      & ( v2_tops_2(esk2_0,esk1_0)
        | ~ v1_compts_1(esk1_0) )
      & ( k6_setfam_1(u1_struct_0(esk1_0),esk2_0) = k1_xboole_0
        | ~ v1_compts_1(esk1_0) )
      & ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
        | X6 = k1_xboole_0
        | ~ r1_tarski(X6,esk2_0)
        | ~ v1_finset_1(X6)
        | k6_setfam_1(u1_struct_0(esk1_0),X6) != k1_xboole_0
        | ~ v1_compts_1(esk1_0) )
      & ( m1_subset_1(esk3_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
        | X7 = k1_xboole_0
        | ~ v2_tops_2(X7,esk1_0)
        | k6_setfam_1(u1_struct_0(esk1_0),X7) != k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
        | v1_compts_1(esk1_0) )
      & ( esk3_1(X7) != k1_xboole_0
        | X7 = k1_xboole_0
        | ~ v2_tops_2(X7,esk1_0)
        | k6_setfam_1(u1_struct_0(esk1_0),X7) != k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
        | v1_compts_1(esk1_0) )
      & ( r1_tarski(esk3_1(X7),X7)
        | X7 = k1_xboole_0
        | ~ v2_tops_2(X7,esk1_0)
        | k6_setfam_1(u1_struct_0(esk1_0),X7) != k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
        | v1_compts_1(esk1_0) )
      & ( v1_finset_1(esk3_1(X7))
        | X7 = k1_xboole_0
        | ~ v2_tops_2(X7,esk1_0)
        | k6_setfam_1(u1_struct_0(esk1_0),X7) != k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
        | v1_compts_1(esk1_0) )
      & ( k6_setfam_1(u1_struct_0(esk1_0),esk3_1(X7)) = k1_xboole_0
        | X7 = k1_xboole_0
        | ~ v2_tops_2(X7,esk1_0)
        | k6_setfam_1(u1_struct_0(esk1_0),X7) != k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
        | v1_compts_1(esk1_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).

cnf(c_0_9,plain,
    ( k6_setfam_1(u1_struct_0(X1),esk8_1(X1)) = k1_xboole_0
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk8_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( v2_tops_2(esk8_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22)))
      | k6_setfam_1(X22,X23) = k1_setfam_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | X1 = k1_xboole_0
    | v1_compts_1(esk1_0)
    | ~ v2_tops_2(X1,esk1_0)
    | k6_setfam_1(u1_struct_0(esk1_0),X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk1_0),esk8_1(esk1_0)) = k1_xboole_0
    | v1_compts_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk8_1(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | v1_compts_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v2_tops_2(esk8_1(esk1_0),esk1_0)
    | v1_compts_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_11])]),c_0_12])).

fof(c_0_20,plain,(
    ! [X11,X12,X13] :
      ( ( X11 != k1_xboole_0
        | ~ v3_finset_1(X11) )
      & ( X12 = k1_xboole_0
        | ~ r1_tarski(X12,X11)
        | ~ v1_finset_1(X12)
        | k1_setfam_1(X12) != k1_xboole_0
        | ~ v3_finset_1(X11) )
      & ( esk4_1(X13) != k1_xboole_0
        | X13 = k1_xboole_0
        | v3_finset_1(X13) )
      & ( r1_tarski(esk4_1(X13),X13)
        | X13 = k1_xboole_0
        | v3_finset_1(X13) )
      & ( v1_finset_1(esk4_1(X13))
        | X13 = k1_xboole_0
        | v3_finset_1(X13) )
      & ( k1_setfam_1(esk4_1(X13)) = k1_xboole_0
        | X13 = k1_xboole_0
        | v3_finset_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_finset_1])])])])])])).

cnf(c_0_21,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( esk8_1(esk1_0) = k1_xboole_0
    | m1_subset_1(esk3_1(esk8_1(esk1_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v1_finset_1(esk3_1(X1))
    | X1 = k1_xboole_0
    | v1_compts_1(esk1_0)
    | ~ v2_tops_2(X1,esk1_0)
    | k6_setfam_1(u1_struct_0(esk1_0),X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk1_0),esk3_1(X1)) = k1_xboole_0
    | X1 = k1_xboole_0
    | v1_compts_1(esk1_0)
    | ~ v2_tops_2(X1,esk1_0)
    | k6_setfam_1(u1_struct_0(esk1_0),X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ v1_finset_1(X1)
    | k1_setfam_1(X1) != k1_xboole_0
    | ~ v3_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k1_setfam_1(esk3_1(esk8_1(esk1_0))) = k6_setfam_1(u1_struct_0(esk1_0),esk3_1(esk8_1(esk1_0)))
    | esk8_1(esk1_0) = k1_xboole_0
    | v1_compts_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( esk8_1(esk1_0) = k1_xboole_0
    | v1_finset_1(esk3_1(esk8_1(esk1_0)))
    | v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk1_0),esk3_1(esk8_1(esk1_0))) = k1_xboole_0
    | esk8_1(esk1_0) = k1_xboole_0
    | v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk3_1(X1),X1)
    | X1 = k1_xboole_0
    | v1_compts_1(esk1_0)
    | ~ v2_tops_2(X1,esk1_0)
    | k6_setfam_1(u1_struct_0(esk1_0),X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( v3_finset_1(esk8_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( esk3_1(esk8_1(esk1_0)) = k1_xboole_0
    | esk8_1(esk1_0) = k1_xboole_0
    | v1_compts_1(esk1_0)
    | ~ v3_finset_1(X1)
    | ~ r1_tarski(esk3_1(esk8_1(esk1_0)),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( esk8_1(esk1_0) = k1_xboole_0
    | r1_tarski(esk3_1(esk8_1(esk1_0)),esk8_1(esk1_0))
    | v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( v3_finset_1(esk8_1(esk1_0))
    | v1_compts_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_compts_1(esk1_0)
    | esk3_1(X1) != k1_xboole_0
    | ~ v2_tops_2(X1,esk1_0)
    | k6_setfam_1(u1_struct_0(esk1_0),X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,negated_conjecture,
    ( esk3_1(esk8_1(esk1_0)) = k1_xboole_0
    | esk8_1(esk1_0) = k1_xboole_0
    | v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_36,plain,
    ( X1 != k1_xboole_0
    | ~ v3_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( esk8_1(esk1_0) = k1_xboole_0
    | v1_compts_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_18]),c_0_19]),c_0_17])).

cnf(c_0_38,plain,
    ( ~ v3_finset_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_36])).

fof(c_0_39,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X34,k1_zfmisc_1(X35))
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | m1_subset_1(X34,k1_zfmisc_1(X35)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_41,negated_conjecture,
    ( v1_compts_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_37]),c_0_38])).

fof(c_0_42,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,X30)
      | ~ r1_tarski(X30,X31)
      | r1_tarski(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk1_0),esk2_0) = k1_xboole_0
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_46,negated_conjecture,
    ( v2_tops_2(esk2_0,esk1_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | ~ v1_compts_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_finset_1(X2)
    | ~ v2_tops_2(X2,X1)
    | k6_setfam_1(u1_struct_0(X1),X2) != k1_xboole_0
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_51,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_41])])).

cnf(c_0_52,negated_conjecture,
    ( v2_tops_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_41])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( r1_tarski(esk4_1(X1),X1)
    | X1 = k1_xboole_0
    | v3_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_41])])).

cnf(c_0_56,negated_conjecture,
    ( ~ v3_finset_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_41]),c_0_10]),c_0_11])]),c_0_12]),c_0_44])])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk4_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk4_1(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X1,esk2_0)
    | ~ v1_finset_1(X1)
    | k6_setfam_1(u1_struct_0(esk1_0),X1) != k1_xboole_0
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_61,plain,
    ( k1_setfam_1(esk4_1(X1)) = k1_xboole_0
    | X1 = k1_xboole_0
    | v3_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( k1_setfam_1(esk4_1(esk2_0)) = k6_setfam_1(u1_struct_0(esk1_0),esk4_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( X1 = k1_xboole_0
    | k6_setfam_1(u1_struct_0(esk1_0),X1) != k1_xboole_0
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_41])])).

cnf(c_0_64,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk1_0),esk4_1(esk2_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_55]),c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( esk4_1(esk2_0) = k1_xboole_0
    | ~ v1_finset_1(esk4_1(esk2_0))
    | ~ r1_tarski(esk4_1(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_59])])).

cnf(c_0_66,negated_conjecture,
    ( esk4_1(esk2_0) = k1_xboole_0
    | ~ v1_finset_1(esk4_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_54]),c_0_55]),c_0_56])).

cnf(c_0_67,plain,
    ( v1_finset_1(esk4_1(X1))
    | X1 = k1_xboole_0
    | v3_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | v3_finset_1(X1)
    | esk4_1(X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_69,negated_conjecture,
    ( esk4_1(esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_55]),c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
