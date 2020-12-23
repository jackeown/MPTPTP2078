%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t41_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:39 EDT 2019

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   34 (  70 expanded)
%              Number of clauses        :   21 (  27 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  199 ( 364 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :   23 (   6 average)
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
    file('/export/starexec/sandbox2/benchmark/tops_2__t41_tops_2.p',d3_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t41_tops_2.p',t4_subset)).

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
    file('/export/starexec/sandbox2/benchmark/tops_2__t41_tops_2.p',t41_tops_2)).

fof(dt_k1_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t41_tops_2.p',dt_k1_tops_2)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t41_tops_2.p',redefinition_k9_subset_1)).

fof(t38_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t41_tops_2.p',t38_tops_2)).

fof(c_0_6,plain,(
    ! [X19,X20,X21,X22,X23,X25,X27] :
      ( ( m1_subset_1(esk5_5(X19,X20,X21,X22,X23),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20))))
        | X22 != k1_tops_2(X19,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20)))))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk5_5(X19,X20,X21,X22,X23),X21)
        | ~ r2_hidden(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20))))
        | X22 != k1_tops_2(X19,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20)))))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( k9_subset_1(u1_struct_0(X19),esk5_5(X19,X20,X21,X22,X23),X20) = X23
        | ~ r2_hidden(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20))))
        | X22 != k1_tops_2(X19,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20)))))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(X25,X21)
        | k9_subset_1(u1_struct_0(X19),X25,X20) != X23
        | r2_hidden(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20))))
        | X22 != k1_tops_2(X19,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20)))))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk6_4(X19,X20,X21,X22),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20))))
        | X22 = k1_tops_2(X19,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20)))))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(esk6_4(X19,X20,X21,X22),X22)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(X27,X21)
        | k9_subset_1(u1_struct_0(X19),X27,X20) != esk6_4(X19,X20,X21,X22)
        | X22 = k1_tops_2(X19,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20)))))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk7_4(X19,X20,X21,X22),k1_zfmisc_1(u1_struct_0(X19)))
        | r2_hidden(esk6_4(X19,X20,X21,X22),X22)
        | X22 = k1_tops_2(X19,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20)))))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk7_4(X19,X20,X21,X22),X21)
        | r2_hidden(esk6_4(X19,X20,X21,X22),X22)
        | X22 = k1_tops_2(X19,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20)))))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( k9_subset_1(u1_struct_0(X19),esk7_4(X19,X20,X21,X22),X20) = esk6_4(X19,X20,X21,X22)
        | r2_hidden(esk6_4(X19,X20,X21,X22),X22)
        | X22 = k1_tops_2(X19,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X19,X20)))))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_2])])])])])).

fof(c_0_7,plain,(
    ! [X70,X71,X72] :
      ( ~ r2_hidden(X70,X71)
      | ~ m1_subset_1(X71,k1_zfmisc_1(X72))
      | m1_subset_1(X70,X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_8,negated_conjecture,(
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

cnf(c_0_9,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X33,X34,X35] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))
      | m1_subset_1(k1_tops_2(X33,X34,X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X33,X34))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).

fof(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & r2_hidden(esk2_0,esk4_0)
    & ~ r2_hidden(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_tops_2(esk1_0,esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X57,X58,X59] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(X57))
      | k9_subset_1(X57,X58,X59) = k3_xboole_0(X58,X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X4,X5) != X1
    | X2 != k1_tops_2(X3,X5,X6)
    | ~ r2_hidden(X4,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X3,X5)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X3,X5))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_tops_2(esk1_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,X5)
    | k9_subset_1(u1_struct_0(X2),X6,X3) != X1
    | ~ r2_hidden(X6,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(k3_xboole_0(esk2_0,esk3_0),k1_tops_2(esk1_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_21,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))
    | k1_tops_2(X1,X3,X4) != k1_tops_2(X1,X3,X5)
    | ~ r2_hidden(X2,X5)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_23,plain,(
    ! [X65,X66,X67] :
      ( ~ l1_pre_topc(X65)
      | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))
      | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X65)))
      | m1_subset_1(k9_subset_1(u1_struct_0(X65),X66,X67),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X65,X67)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_tops_2])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(X1,esk2_0,esk3_0),k1_tops_2(esk1_0,esk3_0,esk4_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_0,X2),k1_tops_2(X1,X2,X3))
    | k1_tops_2(X1,X2,X3) != k1_tops_2(X1,X2,esk4_0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),esk2_0,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_18]),c_0_26]),c_0_27])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X4,X3))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ l1_pre_topc(X4) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_18]),c_0_32]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
