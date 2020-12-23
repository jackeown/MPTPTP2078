%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1319+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:07 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   38 (  73 expanded)
%              Number of clauses        :   27 (  31 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :  271 ( 580 expanded)
%              Number of equality atoms :   40 (  70 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal clause size      :   70 (   6 average)
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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k1_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(t40_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( r1_tarski(X3,X4)
                   => r1_tarski(k1_tops_2(X1,X2,X3),k1_tops_2(X1,X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tops_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_5,plain,(
    ! [X15,X16,X17,X18,X19,X21,X23] :
      ( ( m1_subset_1(esk2_5(X15,X16,X17,X18,X19),k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16))))
        | X18 != k1_tops_2(X15,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16)))))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk2_5(X15,X16,X17,X18,X19),X17)
        | ~ r2_hidden(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16))))
        | X18 != k1_tops_2(X15,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16)))))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( k9_subset_1(u1_struct_0(X15),esk2_5(X15,X16,X17,X18,X19),X16) = X19
        | ~ r2_hidden(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16))))
        | X18 != k1_tops_2(X15,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16)))))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(X21,X17)
        | k9_subset_1(u1_struct_0(X15),X21,X16) != X19
        | r2_hidden(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16))))
        | X18 != k1_tops_2(X15,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16)))))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk3_4(X15,X16,X17,X18),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16))))
        | X18 = k1_tops_2(X15,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16)))))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(esk3_4(X15,X16,X17,X18),X18)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(X23,X17)
        | k9_subset_1(u1_struct_0(X15),X23,X16) != esk3_4(X15,X16,X17,X18)
        | X18 = k1_tops_2(X15,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16)))))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk4_4(X15,X16,X17,X18),k1_zfmisc_1(u1_struct_0(X15)))
        | r2_hidden(esk3_4(X15,X16,X17,X18),X18)
        | X18 = k1_tops_2(X15,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16)))))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk4_4(X15,X16,X17,X18),X17)
        | r2_hidden(esk3_4(X15,X16,X17,X18),X18)
        | X18 = k1_tops_2(X15,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16)))))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( k9_subset_1(u1_struct_0(X15),esk4_4(X15,X16,X17,X18),X16) = esk3_4(X15,X16,X17,X18)
        | r2_hidden(esk3_4(X15,X16,X17,X18),X18)
        | X18 = k1_tops_2(X15,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X15,X16)))))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_2])])])])])).

fof(c_0_6,plain,(
    ! [X31,X32,X33] :
      ( ~ r2_hidden(X31,X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(X33))
      | m1_subset_1(X31,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_7,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X25,X26,X27] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
      | m1_subset_1(k1_tops_2(X25,X26,X27),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X25,X26))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( r1_tarski(X3,X4)
                     => r1_tarski(k1_tops_2(X1,X2,X3),k1_tops_2(X1,X2,X4)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t40_tops_2])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X4,X5) != X1
    | X2 != k1_tops_2(X3,X5,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X3,X5)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X3,X5))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3)
    | ~ r2_hidden(X4,X6) ),
    inference(csr,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k9_subset_1(u1_struct_0(X1),esk2_5(X1,X2,X3,X4,X5),X2) = X5
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | X4 != k1_tops_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_14,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    & r1_tarski(esk7_0,esk8_0)
    & ~ r1_tarski(k1_tops_2(esk5_0,esk6_0,esk7_0),k1_tops_2(esk5_0,esk6_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,X5)
    | k9_subset_1(u1_struct_0(X2),X6,X3) != X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X6,X5) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k9_subset_1(u1_struct_0(X1),esk2_5(X1,X2,X3,X4,X5),X2) = X5
    | X4 != k1_tops_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X5,X4) ),
    inference(csr,[status(thm)],[c_0_13,c_0_8])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,X5)
    | X6 != k1_tops_2(X2,X3,X7)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3)))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(esk2_5(X2,X3,X7,X6,X1),X5)
    | ~ r2_hidden(X1,X6) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17])]),c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_5(X1,X2,X3,X4,X5),X3)
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | X4 != k1_tops_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,esk8_0)
    | X5 != k1_tops_2(X2,X3,X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3)))))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(esk2_5(X2,X3,X6,X5,X1),esk7_0)
    | ~ r2_hidden(X1,X5) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_5(X1,X2,X3,X4,X5),X3)
    | X4 != k1_tops_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X5,X4) ),
    inference(csr,[status(thm)],[c_0_22,c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,esk8_0)
    | X5 != k1_tops_2(X2,X3,esk7_0)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3)))))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,X5) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,esk8_0)
    | k1_tops_2(X2,X3,X5) != k1_tops_2(X2,X3,esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,k1_tops_2(X2,X3,X5)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_12])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(k1_tops_2(X1,X2,X3),X4),k1_tops_2(X1,X2,X5))
    | r1_tarski(k1_tops_2(X1,X2,X3),X4)
    | k1_tops_2(X1,X2,X5) != k1_tops_2(X1,X2,esk8_0)
    | k1_tops_2(X1,X2,X3) != k1_tops_2(X1,X2,esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k1_tops_2(X1,X2,X3),k1_tops_2(X1,X2,X4))
    | k1_tops_2(X1,X2,X4) != k1_tops_2(X1,X2,esk8_0)
    | k1_tops_2(X1,X2,X3) != k1_tops_2(X1,X2,esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k1_tops_2(esk5_0,esk6_0,esk7_0),k1_tops_2(esk5_0,esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k1_tops_2(X1,X2,X3),k1_tops_2(X1,X2,esk8_0))
    | k1_tops_2(X1,X2,X3) != k1_tops_2(X1,X2,esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])]),
    [proof]).

%------------------------------------------------------------------------------
