%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1313+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:06 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 448 expanded)
%              Number of clauses        :   34 ( 160 expanded)
%              Number of leaves         :    4 ( 108 expanded)
%              Depth                    :   11
%              Number of atoms          :  217 (3198 expanded)
%              Number of equality atoms :   17 ( 349 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( v3_pre_topc(X3,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
               => ( v3_pre_topc(X3,X2)
                <=> ? [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                      & v3_pre_topc(X4,X1)
                      & k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) = X3 ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_tops_2])).

fof(c_0_5,plain,(
    ! [X7,X8,X9,X11,X13] :
      ( ( r1_tarski(k2_struct_0(X8),k2_struct_0(X7))
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(X9,u1_pre_topc(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X9),u1_pre_topc(X7))
        | ~ r2_hidden(X9,u1_pre_topc(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( X9 = k9_subset_1(u1_struct_0(X8),esk1_3(X7,X8,X9),k2_struct_0(X8))
        | ~ r2_hidden(X9,u1_pre_topc(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(X11,u1_pre_topc(X7))
        | X9 != k9_subset_1(u1_struct_0(X8),X11,k2_struct_0(X8))
        | r2_hidden(X9,u1_pre_topc(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk2_2(X7,X8),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ r1_tarski(k2_struct_0(X8),k2_struct_0(X7))
        | m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(esk2_2(X7,X8),u1_pre_topc(X8))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(X13,u1_pre_topc(X7))
        | esk2_2(X7,X8) != k9_subset_1(u1_struct_0(X8),X13,k2_struct_0(X8))
        | ~ r1_tarski(k2_struct_0(X8),k2_struct_0(X7))
        | m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk3_2(X7,X8),k1_zfmisc_1(u1_struct_0(X7)))
        | r2_hidden(esk2_2(X7,X8),u1_pre_topc(X8))
        | ~ r1_tarski(k2_struct_0(X8),k2_struct_0(X7))
        | m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk3_2(X7,X8),u1_pre_topc(X7))
        | r2_hidden(esk2_2(X7,X8),u1_pre_topc(X8))
        | ~ r1_tarski(k2_struct_0(X8),k2_struct_0(X7))
        | m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( esk2_2(X7,X8) = k9_subset_1(u1_struct_0(X8),esk3_2(X7,X8),k2_struct_0(X8))
        | r2_hidden(esk2_2(X7,X8),u1_pre_topc(X8))
        | ~ r1_tarski(k2_struct_0(X8),k2_struct_0(X7))
        | m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_6,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_7,plain,(
    ! [X5,X6] :
      ( ( ~ v3_pre_topc(X6,X5)
        | r2_hidden(X6,u1_pre_topc(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( ~ r2_hidden(X6,u1_pre_topc(X5))
        | v3_pre_topc(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X20] :
      ( l1_pre_topc(esk4_0)
      & m1_pre_topc(esk5_0,esk4_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
      & ( ~ v3_pre_topc(esk6_0,esk5_0)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ v3_pre_topc(X20,esk4_0)
        | k9_subset_1(u1_struct_0(esk5_0),X20,k2_struct_0(esk5_0)) != esk6_0 )
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | v3_pre_topc(esk6_0,esk5_0) )
      & ( v3_pre_topc(esk7_0,esk4_0)
        | v3_pre_topc(esk6_0,esk5_0) )
      & ( k9_subset_1(u1_struct_0(esk5_0),esk7_0,k2_struct_0(esk5_0)) = esk6_0
        | v3_pre_topc(esk6_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,u1_pre_topc(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | X3 != k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | v3_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0)
    | v3_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X3)
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_9,c_0_10])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk7_0,u1_pre_topc(esk4_0))
    | v3_pre_topc(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),esk7_0,k2_struct_0(X1)),u1_pre_topc(X1))
    | v3_pre_topc(esk6_0,esk5_0)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),esk7_0,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_13])]),c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_17]),c_0_13])])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk5_0),esk7_0,k2_struct_0(esk5_0)),u1_pre_topc(esk5_0))
    | v3_pre_topc(esk6_0,esk5_0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(esk5_0),esk7_0,k2_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk7_0,k2_struct_0(esk5_0)) = esk6_0
    | v3_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk6_0,u1_pre_topc(esk5_0))
    | ~ v3_pre_topc(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_19]),c_0_20])])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_21,c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk6_0,u1_pre_topc(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_19])]),c_0_24])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_25,c_0_10])).

cnf(c_0_29,plain,
    ( X1 = k9_subset_1(u1_struct_0(X2),esk1_3(X3,X2,X1),k2_struct_0(X2))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_30,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_3(X1,esk5_0,esk6_0),u1_pre_topc(X1))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk1_3(X1,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_19])])).

cnf(c_0_33,plain,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(X2,X1,X3),k2_struct_0(X1)) = X3
    | ~ m1_pre_topc(X1,X2)
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_29,c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( ~ v3_pre_topc(esk6_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v3_pre_topc(X1,esk4_0)
    | k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_19]),c_0_20])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk5_0,esk6_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_17]),c_0_13])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_13])])).

cnf(c_0_38,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk1_3(X1,esk5_0,esk6_0),k2_struct_0(esk5_0)) = esk6_0
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_27]),c_0_19])])).

cnf(c_0_39,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)) != esk6_0
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_40,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk4_0,esk5_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_36]),c_0_37]),c_0_13])])).

cnf(c_0_41,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk1_3(esk4_0,esk5_0,esk6_0),k2_struct_0(esk5_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_17]),c_0_13])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_37])]),
    [proof]).

%------------------------------------------------------------------------------
