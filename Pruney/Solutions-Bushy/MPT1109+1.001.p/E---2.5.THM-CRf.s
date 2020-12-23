%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1109+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 (4288 expanded)
%              Number of clauses        :   75 (1815 expanded)
%              Number of leaves         :    7 (1020 expanded)
%              Depth                    :   19
%              Number of atoms          :  382 (20674 expanded)
%              Number of equality atoms :   59 (5592 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t31_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( l1_pre_topc(X3)
             => ! [X4] :
                  ( l1_pre_topc(X4)
                 => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                      & g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
                      & m1_pre_topc(X3,X1) )
                   => m1_pre_topc(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(c_0_7,plain,(
    ! [X18,X19,X20,X21] :
      ( ( X18 = X20
        | g1_pre_topc(X18,X19) != g1_pre_topc(X20,X21)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18))) )
      & ( X19 = X21
        | g1_pre_topc(X18,X19) != g1_pre_topc(X20,X21)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_8,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | m1_subset_1(u1_pre_topc(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( l1_pre_topc(X3)
               => ! [X4] :
                    ( l1_pre_topc(X4)
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                        & g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
                        & m1_pre_topc(X3,X1) )
                     => m1_pre_topc(X4,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_pre_topc])).

cnf(c_0_10,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & l1_pre_topc(esk5_0)
    & l1_pre_topc(esk6_0)
    & l1_pre_topc(esk7_0)
    & g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    & g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    & m1_pre_topc(esk6_0,esk4_0)
    & ~ m1_pre_topc(esk7_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | k2_struct_0(X5) = u1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_19,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_20,negated_conjecture,
    ( u1_pre_topc(esk7_0) = X1
    | g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

fof(c_0_21,plain,(
    ! [X6,X7,X8,X10,X12] :
      ( ( r1_tarski(k2_struct_0(X7),k2_struct_0(X6))
        | ~ m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk1_3(X6,X7,X8),k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(X8,u1_pre_topc(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X8),u1_pre_topc(X6))
        | ~ r2_hidden(X8,u1_pre_topc(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( X8 = k9_subset_1(u1_struct_0(X7),esk1_3(X6,X7,X8),k2_struct_0(X7))
        | ~ r2_hidden(X8,u1_pre_topc(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(X10,u1_pre_topc(X6))
        | X8 != k9_subset_1(u1_struct_0(X7),X10,k2_struct_0(X7))
        | r2_hidden(X8,u1_pre_topc(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk2_2(X6,X7),k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r1_tarski(k2_struct_0(X7),k2_struct_0(X6))
        | m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( ~ r2_hidden(esk2_2(X6,X7),u1_pre_topc(X7))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(X12,u1_pre_topc(X6))
        | esk2_2(X6,X7) != k9_subset_1(u1_struct_0(X7),X12,k2_struct_0(X7))
        | ~ r1_tarski(k2_struct_0(X7),k2_struct_0(X6))
        | m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk3_2(X6,X7),k1_zfmisc_1(u1_struct_0(X6)))
        | r2_hidden(esk2_2(X6,X7),u1_pre_topc(X7))
        | ~ r1_tarski(k2_struct_0(X7),k2_struct_0(X6))
        | m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk3_2(X6,X7),u1_pre_topc(X6))
        | r2_hidden(esk2_2(X6,X7),u1_pre_topc(X7))
        | ~ r1_tarski(k2_struct_0(X7),k2_struct_0(X6))
        | m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( esk2_2(X6,X7) = k9_subset_1(u1_struct_0(X7),esk3_2(X6,X7),k2_struct_0(X7))
        | r2_hidden(esk2_2(X6,X7),u1_pre_topc(X7))
        | ~ r1_tarski(k2_struct_0(X7),k2_struct_0(X6))
        | m1_pre_topc(X7,X6)
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_22,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_23,negated_conjecture,
    ( u1_pre_topc(esk4_0) = X1
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_16]),c_0_17])])).

cnf(c_0_24,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( u1_pre_topc(esk7_0) = u1_pre_topc(esk6_0) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( u1_pre_topc(esk4_0) = u1_pre_topc(esk5_0) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( esk2_2(X1,X2) = k9_subset_1(u1_struct_0(X2),esk3_2(X1,X2),k2_struct_0(X2))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_26]),c_0_15])])).

cnf(c_0_34,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk6_0)) = g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_26])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( u1_struct_0(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk5_0)) = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_30])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,plain,
    ( k9_subset_1(u1_struct_0(X1),esk3_2(X2,X1),k2_struct_0(X1)) = esk2_2(X2,X1)
    | r2_hidden(esk2_2(X2,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X2)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk7_0) = X1
    | g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) != g1_pre_topc(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_33]),c_0_34])).

cnf(c_0_41,plain,
    ( r1_tarski(u1_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(X1,X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_30]),c_0_17])]),c_0_37])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,plain,
    ( r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,plain,
    ( r2_hidden(X3,u1_pre_topc(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | X3 != k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,plain,
    ( k9_subset_1(u1_struct_0(X1),esk3_2(X2,X1),u1_struct_0(X1)) = esk2_2(X2,X1)
    | r2_hidden(esk2_2(X2,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_32])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk7_0) = u1_struct_0(esk6_0) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_32])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk5_0) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_32])).

cnf(c_0_52,plain,
    ( r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_32])).

cnf(c_0_53,plain,
    ( r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_32])).

cnf(c_0_54,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_46,c_0_28])])).

cnf(c_0_55,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),esk3_2(X1,esk7_0),u1_struct_0(esk6_0)) = esk2_2(X1,esk7_0)
    | r2_hidden(esk2_2(X1,esk7_0),u1_pre_topc(esk6_0))
    | m1_pre_topc(esk7_0,X1)
    | ~ r1_tarski(u1_struct_0(esk6_0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_26]),c_0_15])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk5_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_17])])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_58,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_59,negated_conjecture,
    ( ~ m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk2_2(X1,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | m1_pre_topc(esk7_0,X1)
    | ~ r1_tarski(u1_struct_0(esk6_0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_15])])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_32])).

cnf(c_0_62,plain,
    ( r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_32])).

cnf(c_0_63,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_32]),c_0_28])).

cnf(c_0_64,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),esk3_2(esk5_0,esk7_0),u1_struct_0(esk6_0)) = esk2_2(esk5_0,esk7_0)
    | r2_hidden(esk2_2(esk5_0,esk7_0),u1_pre_topc(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk2_2(esk5_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_56]),c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk7_0),u1_pre_topc(esk6_0))
    | m1_subset_1(esk3_2(X1,esk7_0),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(esk7_0,X1)
    | ~ r1_tarski(u1_struct_0(esk6_0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_48]),c_0_26]),c_0_15])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk7_0),u1_pre_topc(esk6_0))
    | r2_hidden(esk3_2(X1,esk7_0),u1_pre_topc(X1))
    | m1_pre_topc(esk7_0,X1)
    | ~ r1_tarski(u1_struct_0(esk6_0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_48]),c_0_26]),c_0_15])])).

cnf(c_0_68,plain,
    ( m1_pre_topc(X2,X1)
    | ~ r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | esk2_2(X1,X2) != k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,esk7_0),u1_pre_topc(esk6_0))
    | ~ r2_hidden(esk3_2(esk5_0,esk7_0),u1_pre_topc(X1))
    | ~ m1_subset_1(esk3_2(esk5_0,esk7_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,esk7_0),u1_pre_topc(esk6_0))
    | m1_subset_1(esk3_2(esk5_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_56]),c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk7_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk2_2(esk5_0,esk7_0),u1_pre_topc(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_56]),c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_72,negated_conjecture,
    ( m1_pre_topc(esk7_0,X1)
    | esk2_2(X1,esk7_0) != k9_subset_1(u1_struct_0(esk6_0),X2,k2_struct_0(esk7_0))
    | ~ r2_hidden(esk2_2(X1,esk7_0),u1_pre_topc(esk6_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_struct_0(esk7_0),k2_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_26]),c_0_15])]),c_0_48])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,esk7_0),u1_pre_topc(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_50]),c_0_30]),c_0_58]),c_0_17])]),c_0_70]),c_0_71])).

cnf(c_0_74,plain,
    ( X1 = k9_subset_1(u1_struct_0(X2),esk1_3(X3,X2,X1),k2_struct_0(X2))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_75,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),X1,k2_struct_0(esk7_0)) != esk2_2(esk5_0,esk7_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_struct_0(esk7_0),k2_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_57])]),c_0_59])).

cnf(c_0_76,plain,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(X2,X1,X3),k2_struct_0(X1)) = X3
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_74,c_0_28])).

cnf(c_0_77,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_78,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),X1,u1_struct_0(esk6_0)) != esk2_2(esk5_0,esk7_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(u1_struct_0(esk6_0),k2_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_32]),c_0_48]),c_0_48]),c_0_15])])).

cnf(c_0_79,plain,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(X2,X1,X3),u1_struct_0(X1)) = X3
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_32]),c_0_28])).

cnf(c_0_80,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_77,c_0_28])).

cnf(c_0_81,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(esk1_3(X1,esk6_0,esk2_2(esk5_0,esk7_0)),u1_pre_topc(esk5_0))
    | ~ m1_subset_1(esk1_3(X1,esk6_0,esk2_2(esk5_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(u1_struct_0(esk6_0),k2_struct_0(esk5_0))
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79])]),c_0_73]),c_0_65])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_50]),c_0_17])])).

cnf(c_0_84,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_81,c_0_28])).

cnf(c_0_85,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk4_0,esk6_0,esk2_2(esk5_0,esk7_0)),u1_pre_topc(esk5_0))
    | ~ r1_tarski(u1_struct_0(esk6_0),k2_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_58]),c_0_17]),c_0_73]),c_0_65])])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,X1,X2),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_30]),c_0_17])])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(esk6_0),k2_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_73]),c_0_65]),c_0_58])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(esk6_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_32]),c_0_57])])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_56]),c_0_58])]),
    [proof]).

%------------------------------------------------------------------------------
