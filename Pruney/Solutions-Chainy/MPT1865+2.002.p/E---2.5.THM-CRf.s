%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:43 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 141 expanded)
%              Number of clauses        :   38 (  57 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  187 ( 631 expanded)
%              Number of equality atoms :   30 (  94 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v4_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k1_tarski(X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t60_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => ( ( r2_hidden(X3,X2)
          & X1 != X3 )
        | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d6_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r1_tarski(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v4_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tex_2(X2,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ ( r2_hidden(X3,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( v4_pre_topc(X4,X1)
                              & k9_subset_1(u1_struct_0(X1),X2,X4) = k1_tarski(X3) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_tex_2])).

fof(c_0_12,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | ~ v1_xboole_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_13,negated_conjecture,(
    ! [X37] :
      ( l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & v2_tex_2(esk4_0,esk3_0)
      & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
      & r2_hidden(esk5_0,esk4_0)
      & ( ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v4_pre_topc(X37,esk3_0)
        | k9_subset_1(u1_struct_0(esk3_0),esk4_0,X37) != k1_tarski(esk5_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,X20)
      | v1_xboole_0(X20)
      | r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X16,X17,X18] :
      ( ( r2_hidden(X18,X17)
        | k3_xboole_0(k2_tarski(X16,X18),X17) = k1_tarski(X16)
        | ~ r2_hidden(X16,X17) )
      & ( X16 != X18
        | k3_xboole_0(k2_tarski(X16,X18),X17) = k1_tarski(X16)
        | ~ r2_hidden(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).

fof(c_0_20,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | r2_hidden(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | k3_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_27,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_28,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_29,plain,
    ( k3_xboole_0(k2_tarski(X3,X1),X2) = k2_tarski(X3,X3)
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v4_pre_topc(X1,esk3_0)
    | k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_33,plain,(
    ! [X28,X29,X30,X33] :
      ( ( m1_subset_1(esk1_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))
        | ~ r1_tarski(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ v2_tex_2(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( v4_pre_topc(esk1_3(X28,X29,X30),X28)
        | ~ r1_tarski(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ v2_tex_2(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( k9_subset_1(u1_struct_0(X28),X29,esk1_3(X28,X29,X30)) = X30
        | ~ r1_tarski(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ v2_tex_2(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(esk2_2(X28,X29),k1_zfmisc_1(u1_struct_0(X28)))
        | v2_tex_2(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( r1_tarski(esk2_2(X28,X29),X29)
        | v2_tex_2(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ v4_pre_topc(X33,X28)
        | k9_subset_1(u1_struct_0(X28),X29,X33) != esk2_2(X28,X29)
        | v2_tex_2(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).

fof(c_0_34,plain,(
    ! [X26,X27] :
      ( ~ r2_hidden(X26,X27)
      | ~ r1_tarski(X27,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk3_0),k2_tarski(esk5_0,X1)) = k2_tarski(esk5_0,esk5_0)
    | r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

fof(c_0_37,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_38,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1) != k2_tarski(esk5_0,esk5_0)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_24])).

cnf(c_0_39,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | r1_tarski(k2_tarski(esk5_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( X1 != k2_tarski(esk5_0,esk5_0)
    | ~ v4_pre_topc(esk1_3(esk3_0,esk4_0,X1),esk3_0)
    | ~ m1_subset_1(esk1_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_16])])).

cnf(c_0_46,plain,
    ( v4_pre_topc(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_47,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k2_tarski(esk5_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(u1_struct_0(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( X1 != k2_tarski(esk5_0,esk5_0)
    | ~ m1_subset_1(esk1_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_40]),c_0_41]),c_0_16])])).

cnf(c_0_51,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_tarski(esk5_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( X1 != k2_tarski(esk5_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_40]),c_0_41]),c_0_16])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(esk4_0,k2_tarski(esk5_0,X1)) = k2_tarski(esk5_0,esk5_0)
    | r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k2_tarski(esk5_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_56]),c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_59,c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.13/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t33_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tex_2)).
% 0.13/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.13/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.38  fof(t60_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.38  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.13/0.38  fof(d6_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 0.13/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.38  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3))))))))))), inference(assume_negation,[status(cth)],[t33_tex_2])).
% 0.13/0.38  fof(c_0_12, plain, ![X23, X24, X25]:(~r2_hidden(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X25))|~v1_xboole_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ![X37]:(l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(v2_tex_2(esk4_0,esk3_0)&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(r2_hidden(esk5_0,esk4_0)&(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk3_0)))|(~v4_pre_topc(X37,esk3_0)|k9_subset_1(u1_struct_0(esk3_0),esk4_0,X37)!=k1_tarski(esk5_0)))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X19, X20]:(~m1_subset_1(X19,X20)|(v1_xboole_0(X20)|r2_hidden(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.38  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_19, plain, ![X16, X17, X18]:((r2_hidden(X18,X17)|k3_xboole_0(k2_tarski(X16,X18),X17)=k1_tarski(X16)|~r2_hidden(X16,X17))&(X16!=X18|k3_xboole_0(k2_tarski(X16,X18),X17)=k1_tarski(X16)|~r2_hidden(X16,X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|r2_hidden(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X2)|k3_xboole_0(k2_tarski(X3,X1),X2)=k1_tarski(X3)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_27, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.38  fof(c_0_28, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.13/0.38  cnf(c_0_29, plain, (k3_xboole_0(k2_tarski(X3,X1),X2)=k2_tarski(X3,X3)|r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.38  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v4_pre_topc(X1,esk3_0)|k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1)!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_33, plain, ![X28, X29, X30, X33]:(((m1_subset_1(esk1_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))|~r1_tarski(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~v2_tex_2(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&((v4_pre_topc(esk1_3(X28,X29,X30),X28)|~r1_tarski(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~v2_tex_2(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(k9_subset_1(u1_struct_0(X28),X29,esk1_3(X28,X29,X30))=X30|~r1_tarski(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~v2_tex_2(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))))&((m1_subset_1(esk2_2(X28,X29),k1_zfmisc_1(u1_struct_0(X28)))|v2_tex_2(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&((r1_tarski(esk2_2(X28,X29),X29)|v2_tex_2(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X28)))|(~v4_pre_topc(X33,X28)|k9_subset_1(u1_struct_0(X28),X29,X33)!=esk2_2(X28,X29))|v2_tex_2(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).
% 0.13/0.38  fof(c_0_34, plain, ![X26, X27]:(~r2_hidden(X26,X27)|~r1_tarski(X27,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.38  cnf(c_0_35, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k3_xboole_0(u1_struct_0(esk3_0),k2_tarski(esk5_0,X1))=k2_tarski(esk5_0,esk5_0)|r2_hidden(X1,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.13/0.38  fof(c_0_37, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1)!=k2_tarski(esk5_0,esk5_0)|~v4_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_32, c_0_24])).
% 0.13/0.38  cnf(c_0_39, plain, (k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3))=X3|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|r1_tarski(k2_tarski(esk5_0,esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.38  cnf(c_0_44, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (X1!=k2_tarski(esk5_0,esk5_0)|~v4_pre_topc(esk1_3(esk3_0,esk4_0,X1),esk3_0)|~m1_subset_1(esk1_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_16])])).
% 0.13/0.38  cnf(c_0_46, plain, (v4_pre_topc(esk1_3(X1,X2,X3),X1)|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  fof(c_0_47, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r1_tarski(k2_tarski(esk5_0,esk5_0),u1_struct_0(esk3_0))|~r1_tarski(u1_struct_0(esk3_0),X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_35, c_0_44])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (X1!=k2_tarski(esk5_0,esk5_0)|~m1_subset_1(esk1_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_40]), c_0_41]), c_0_16])])).
% 0.13/0.38  cnf(c_0_51, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_tarski(esk5_0,esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (X1!=k2_tarski(esk5_0,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_40]), c_0_41]), c_0_16])])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (k3_xboole_0(esk4_0,k2_tarski(esk5_0,X1))=k2_tarski(esk5_0,esk5_0)|r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_26]), c_0_31])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (~r1_tarski(k2_tarski(esk5_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_56]), c_0_57])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_58])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_59, c_0_49]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 61
% 0.13/0.38  # Proof object clause steps            : 38
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 27
% 0.13/0.38  # Proof object clause conjectures      : 24
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 18
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 18
% 0.13/0.38  # Proof object simplifying inferences  : 17
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 13
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 25
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 24
% 0.13/0.38  # Processed clauses                    : 102
% 0.13/0.38  # ...of these trivial                  : 6
% 0.13/0.38  # ...subsumed                          : 14
% 0.13/0.38  # ...remaining for further processing  : 82
% 0.13/0.38  # Other redundant clauses eliminated   : 1
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 5
% 0.13/0.38  # Backward-rewritten                   : 4
% 0.13/0.38  # Generated clauses                    : 241
% 0.13/0.38  # ...of the previous two non-trivial   : 213
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 240
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 1
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 72
% 0.13/0.38  #    Positive orientable unit clauses  : 21
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 10
% 0.13/0.38  #    Non-unit-clauses                  : 40
% 0.13/0.38  # Current number of unprocessed clauses: 133
% 0.13/0.38  # ...number of literals in the above   : 388
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 10
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 540
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 178
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 9
% 0.13/0.38  # Unit Clause-clause subsumption calls : 129
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 36
% 0.13/0.38  # BW rewrite match successes           : 6
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5532
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.034 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.040 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
