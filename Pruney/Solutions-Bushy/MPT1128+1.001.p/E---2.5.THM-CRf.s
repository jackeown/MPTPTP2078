%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1128+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 (1769 expanded)
%              Number of clauses        :   65 ( 759 expanded)
%              Number of leaves         :   12 ( 450 expanded)
%              Depth                    :   23
%              Number of atoms          :  343 (6482 expanded)
%              Number of equality atoms :   42 ( 582 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(t59_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(c_0_12,plain,(
    ! [X25,X26,X27,X28] :
      ( ( X25 = X27
        | g1_pre_topc(X25,X26) != g1_pre_topc(X27,X28)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25))) )
      & ( X26 = X28
        | g1_pre_topc(X25,X26) != g1_pre_topc(X27,X28)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_13,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | m1_subset_1(u1_pre_topc(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_14,plain,(
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

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | l1_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_16,plain,(
    ! [X6] :
      ( ~ l1_struct_0(X6)
      | k2_struct_0(X6) = u1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_17,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_18,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
           => m1_pre_topc(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t59_pre_topc])).

cnf(c_0_22,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( u1_struct_0(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X15,X16] :
      ( ( v1_pre_topc(g1_pre_topc(X15,X16))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( l1_pre_topc(g1_pre_topc(X15,X16))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    & ~ m1_pre_topc(esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_30,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ l1_pre_topc(g1_pre_topc(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_33,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk5_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_35])).

cnf(c_0_39,plain,
    ( esk2_2(X1,X2) = k9_subset_1(u1_struct_0(X2),esk3_2(X1,X2),k2_struct_0(X2))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,plain,
    ( r1_tarski(k2_struct_0(X1),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_pre_topc(X1,g1_pre_topc(X2,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k9_subset_1(u1_struct_0(X1),esk3_2(X2,X1),k2_struct_0(X1)) = esk2_2(X2,X1)
    | r2_hidden(esk2_2(X2,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X2)
    | ~ r1_tarski(k2_struct_0(X1),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_19]),c_0_42])])).

cnf(c_0_46,negated_conjecture,
    ( ~ m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk3_2(esk4_0,esk5_0),k2_struct_0(esk5_0)) = esk2_2(esk4_0,esk5_0)
    | r2_hidden(esk2_2(esk4_0,esk5_0),u1_pre_topc(esk5_0))
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_42])]),c_0_46])).

fof(c_0_48,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X34))
      | m1_subset_1(X32,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_49,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X18))
      | m1_subset_1(k9_subset_1(X18,X19,X20),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_50,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk3_2(esk4_0,esk5_0),k2_struct_0(esk5_0)) = esk2_2(esk4_0,esk5_0)
    | r2_hidden(esk2_2(esk4_0,esk5_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_19]),c_0_42])])).

fof(c_0_51,plain,(
    ! [X17] :
      ( ~ l1_struct_0(X17)
      | m1_subset_1(k2_struct_0(X17),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_52,plain,
    ( r2_hidden(X3,u1_pre_topc(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | X3 != k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk3_2(esk4_0,esk5_0),u1_struct_0(esk5_0)) = esk2_2(esk4_0,esk5_0)
    | r2_hidden(esk2_2(esk4_0,esk5_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_31]),c_0_45])])).

cnf(c_0_56,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_52,c_0_23])])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),u1_pre_topc(esk5_0))
    | m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_25])).

cnf(c_0_61,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_62,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),u1_pre_topc(esk5_0))
    | m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_45])])).

cnf(c_0_64,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_19])).

cnf(c_0_65,plain,
    ( r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(esk3_2(esk4_0,esk5_0),u1_pre_topc(X1))
    | ~ m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_50])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_63]),c_0_45])])).

cnf(c_0_68,plain,
    ( u1_pre_topc(g1_pre_topc(X1,X2)) = X2
    | ~ v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ l1_pre_topc(g1_pre_topc(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27])])).

cnf(c_0_69,plain,
    ( r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_31])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(esk3_2(esk4_0,esk5_0),u1_pre_topc(X1))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_71,plain,
    ( u1_pre_topc(g1_pre_topc(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_33]),c_0_34])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk3_2(esk4_0,esk5_0),u1_pre_topc(esk4_0))
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_44]),c_0_45]),c_0_42])]),c_0_46])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(esk3_2(esk4_0,esk5_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_pre_topc(esk5_0,g1_pre_topc(X2,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_34])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),u1_pre_topc(esk4_0))
    | r2_hidden(esk2_2(esk4_0,esk5_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_19]),c_0_42])])).

cnf(c_0_75,plain,
    ( m1_pre_topc(X2,X1)
    | ~ r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | esk2_2(X1,X2) != k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),u1_pre_topc(esk5_0))
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_pre_topc(esk5_0,g1_pre_topc(X1,u1_pre_topc(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,plain,
    ( m1_pre_topc(X1,X2)
    | esk2_2(X2,X1) != k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1))
    | ~ r2_hidden(esk2_2(X2,X1),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_75,c_0_58])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_19]),c_0_35]),c_0_42])])).

cnf(c_0_79,plain,
    ( X1 = k9_subset_1(u1_struct_0(X2),esk1_3(X3,X2,X1),k2_struct_0(X2))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_80,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_81,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),X1,k2_struct_0(esk5_0)) != esk2_2(esk4_0,esk5_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_45]),c_0_42])]),c_0_46])).

cnf(c_0_82,plain,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(X2,X1,X3),k2_struct_0(X1)) = X3
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_79,c_0_23])).

cnf(c_0_83,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_80,c_0_23])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(esk1_3(X1,esk5_0,esk2_2(esk4_0,esk5_0)),u1_pre_topc(esk4_0))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk4_0))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82])]),c_0_78]),c_0_67])])).

cnf(c_0_85,plain,
    ( r2_hidden(esk1_3(g1_pre_topc(X1,X2),X3,X4),X2)
    | ~ r2_hidden(X4,u1_pre_topc(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_pre_topc(X3,g1_pre_topc(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_71]),c_0_34])).

cnf(c_0_86,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk4_0))
    | ~ m1_pre_topc(esk5_0,g1_pre_topc(X1,u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_78]),c_0_67])]),c_0_34])).

cnf(c_0_87,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | ~ r1_tarski(k2_struct_0(esk5_0),k2_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_35])).

cnf(c_0_88,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_31]),c_0_42])]),c_0_44])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_19]),c_0_42])]),
    [proof]).

%------------------------------------------------------------------------------
