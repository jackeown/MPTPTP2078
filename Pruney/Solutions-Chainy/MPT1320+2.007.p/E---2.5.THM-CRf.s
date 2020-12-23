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
% DateTime   : Thu Dec  3 11:13:25 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   24 (  39 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :  180 ( 270 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal clause size      :   70 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
                 => ( X4 = k1_tops_2(X1,X2,X3)
                  <=> ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
                       => ( r2_hidden(X5,X4)
                        <=> ? [X6] :
                              ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
                              & r2_hidden(X6,X3)
                              & k9_subset_1(u1_struct_0(X1),X6,X2) = X5 ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_2)).

fof(dt_k1_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(t38_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

fof(t41_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( r2_hidden(X2,X4)
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_2)).

fof(c_0_4,plain,(
    ! [X7,X8,X9,X10,X11,X13,X15] :
      ( ( m1_subset_1(esk1_5(X7,X8,X9,X10,X11),k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8))))
        | X10 != k1_tops_2(X7,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk1_5(X7,X8,X9,X10,X11),X9)
        | ~ r2_hidden(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8))))
        | X10 != k1_tops_2(X7,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( k9_subset_1(u1_struct_0(X7),esk1_5(X7,X8,X9,X10,X11),X8) = X11
        | ~ r2_hidden(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8))))
        | X10 != k1_tops_2(X7,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(X13,X9)
        | k9_subset_1(u1_struct_0(X7),X13,X8) != X11
        | r2_hidden(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8))))
        | X10 != k1_tops_2(X7,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk2_4(X7,X8,X9,X10),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8))))
        | X10 = k1_tops_2(X7,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(esk2_4(X7,X8,X9,X10),X10)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(X15,X9)
        | k9_subset_1(u1_struct_0(X7),X15,X8) != esk2_4(X7,X8,X9,X10)
        | X10 = k1_tops_2(X7,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk3_4(X7,X8,X9,X10),k1_zfmisc_1(u1_struct_0(X7)))
        | r2_hidden(esk2_4(X7,X8,X9,X10),X10)
        | X10 = k1_tops_2(X7,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk3_4(X7,X8,X9,X10),X9)
        | r2_hidden(esk2_4(X7,X8,X9,X10),X10)
        | X10 = k1_tops_2(X7,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( k9_subset_1(u1_struct_0(X7),esk3_4(X7,X8,X9,X10),X8) = esk2_4(X7,X8,X9,X10)
        | r2_hidden(esk2_4(X7,X8,X9,X10),X10)
        | X10 = k1_tops_2(X7,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_2])])])])])).

fof(c_0_5,plain,(
    ! [X17,X18,X19] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
      | m1_subset_1(k1_tops_2(X17,X18,X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X17,X18))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).

cnf(c_0_6,plain,
    ( r2_hidden(X5,X6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,X3)
    | k9_subset_1(u1_struct_0(X2),X1,X4) != X5
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4))))
    | X6 != k1_tops_2(X2,X4,X3)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X20,X21,X22] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
      | m1_subset_1(k9_subset_1(u1_struct_0(X20),X21,X22),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X20,X22)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_tops_2])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( r2_hidden(X2,X4)
                     => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_tops_2])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,X5)
    | k9_subset_1(u1_struct_0(X2),X6,X3) != X1
    | ~ r2_hidden(X6,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_11,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & r2_hidden(esk5_0,esk7_0)
    & ~ r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))
    | k9_subset_1(u1_struct_0(X1),X5,X3) != k9_subset_1(u1_struct_0(X1),X2,X3)
    | k1_tops_2(X1,X3,X4) != k1_tops_2(X1,X3,X6)
    | ~ r2_hidden(X5,X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))
    | k9_subset_1(u1_struct_0(X1),esk5_0,X3) != k9_subset_1(u1_struct_0(X1),X2,X3)
    | k1_tops_2(X1,X3,X4) != k1_tops_2(X1,X3,esk7_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),esk5_0,X2),k1_tops_2(X1,X2,X3))
    | k1_tops_2(X1,X2,X3) != k1_tops_2(X1,X2,esk7_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),esk5_0,X2),k1_tops_2(X1,X2,esk7_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:03:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(d3_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))=>(X4=k1_tops_2(X1,X2,X3)<=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))=>(r2_hidden(X5,X4)<=>?[X6]:((m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X6,X3))&k9_subset_1(u1_struct_0(X1),X6,X2)=X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_2)).
% 0.14/0.38  fof(dt_k1_tops_2, axiom, ![X1, X2, X3]:(((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))=>m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_2)).
% 0.14/0.38  fof(t38_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tops_2)).
% 0.14/0.38  fof(t41_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r2_hidden(X2,X4)=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_2)).
% 0.14/0.38  fof(c_0_4, plain, ![X7, X8, X9, X10, X11, X13, X15]:(((((m1_subset_1(esk1_5(X7,X8,X9,X10,X11),k1_zfmisc_1(u1_struct_0(X7)))|~r2_hidden(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8))))|X10!=k1_tops_2(X7,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7))&(r2_hidden(esk1_5(X7,X8,X9,X10,X11),X9)|~r2_hidden(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8))))|X10!=k1_tops_2(X7,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7)))&(k9_subset_1(u1_struct_0(X7),esk1_5(X7,X8,X9,X10,X11),X8)=X11|~r2_hidden(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8))))|X10!=k1_tops_2(X7,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7)))&(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X7)))|~r2_hidden(X13,X9)|k9_subset_1(u1_struct_0(X7),X13,X8)!=X11|r2_hidden(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8))))|X10!=k1_tops_2(X7,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7)))&((m1_subset_1(esk2_4(X7,X8,X9,X10),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8))))|X10=k1_tops_2(X7,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7))&((~r2_hidden(esk2_4(X7,X8,X9,X10),X10)|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X7)))|~r2_hidden(X15,X9)|k9_subset_1(u1_struct_0(X7),X15,X8)!=esk2_4(X7,X8,X9,X10))|X10=k1_tops_2(X7,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7))&(((m1_subset_1(esk3_4(X7,X8,X9,X10),k1_zfmisc_1(u1_struct_0(X7)))|r2_hidden(esk2_4(X7,X8,X9,X10),X10)|X10=k1_tops_2(X7,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7))&(r2_hidden(esk3_4(X7,X8,X9,X10),X9)|r2_hidden(esk2_4(X7,X8,X9,X10),X10)|X10=k1_tops_2(X7,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7)))&(k9_subset_1(u1_struct_0(X7),esk3_4(X7,X8,X9,X10),X8)=esk2_4(X7,X8,X9,X10)|r2_hidden(esk2_4(X7,X8,X9,X10),X10)|X10=k1_tops_2(X7,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X7,X8)))))|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_2])])])])])).
% 0.14/0.38  fof(c_0_5, plain, ![X17, X18, X19]:(~l1_pre_topc(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|m1_subset_1(k1_tops_2(X17,X18,X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X17,X18)))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).
% 0.14/0.38  cnf(c_0_6, plain, (r2_hidden(X5,X6)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,X3)|k9_subset_1(u1_struct_0(X2),X1,X4)!=X5|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4))))|X6!=k1_tops_2(X2,X4,X3)|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4)))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.38  cnf(c_0_7, plain, (m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  fof(c_0_8, plain, ![X20, X21, X22]:(~l1_pre_topc(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|m1_subset_1(k9_subset_1(u1_struct_0(X20),X21,X22),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X20,X22))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_tops_2])])])).
% 0.14/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r2_hidden(X2,X4)=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4)))))))), inference(assume_negation,[status(cth)],[t41_tops_2])).
% 0.14/0.38  cnf(c_0_10, plain, (r2_hidden(X1,k1_tops_2(X2,X3,X4))|k1_tops_2(X2,X3,X4)!=k1_tops_2(X2,X3,X5)|k9_subset_1(u1_struct_0(X2),X6,X3)!=X1|~r2_hidden(X6,X5)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.14/0.38  cnf(c_0_11, plain, (m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  fof(c_0_12, negated_conjecture, (l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&(r2_hidden(esk5_0,esk7_0)&~r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.14/0.38  cnf(c_0_13, plain, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))|k9_subset_1(u1_struct_0(X1),X5,X3)!=k9_subset_1(u1_struct_0(X1),X2,X3)|k1_tops_2(X1,X3,X4)!=k1_tops_2(X1,X3,X6)|~r2_hidden(X5,X6)|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))|k9_subset_1(u1_struct_0(X1),esk5_0,X3)!=k9_subset_1(u1_struct_0(X1),X2,X3)|k1_tops_2(X1,X3,X4)!=k1_tops_2(X1,X3,esk7_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(X1),esk5_0,X2),k1_tops_2(X1,X2,X3))|k1_tops_2(X1,X2,X3)!=k1_tops_2(X1,X2,esk7_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (~r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(X1),esk5_0,X2),k1_tops_2(X1,X2,esk7_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 24
% 0.14/0.38  # Proof object clause steps            : 15
% 0.14/0.38  # Proof object formula steps           : 9
% 0.14/0.38  # Proof object conjectures             : 13
% 0.14/0.38  # Proof object clause conjectures      : 10
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 9
% 0.14/0.38  # Proof object initial formulas used   : 4
% 0.14/0.38  # Proof object generating inferences   : 6
% 0.14/0.38  # Proof object simplifying inferences  : 5
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 4
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 17
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 17
% 0.14/0.38  # Processed clauses                    : 40
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 1
% 0.14/0.38  # ...remaining for further processing  : 39
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 16
% 0.14/0.38  # ...of the previous two non-trivial   : 14
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 14
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 22
% 0.14/0.38  #    Positive orientable unit clauses  : 5
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 16
% 0.14/0.38  # Current number of unprocessed clauses: 7
% 0.14/0.38  # ...number of literals in the above   : 101
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 17
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 160
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 1
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 0
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3883
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.035 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
