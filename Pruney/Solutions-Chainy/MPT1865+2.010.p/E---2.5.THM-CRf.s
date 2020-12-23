%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:44 EST 2020

% Result     : Theorem 0.23s
% Output     : CNFRefutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 201 expanded)
%              Number of clauses        :   41 (  82 expanded)
%              Number of leaves         :   10 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  206 ( 929 expanded)
%              Number of equality atoms :   28 ( 109 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X18] : m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_12,plain,(
    ! [X17] : k2_subset_1(X17) = X17 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_13,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | ~ v1_xboole_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_14,negated_conjecture,(
    ! [X35] :
      ( l1_pre_topc(esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
      & v2_tex_2(esk5_0,esk4_0)
      & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
      & r2_hidden(esk6_0,esk5_0)
      & ( ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ v4_pre_topc(X35,esk4_0)
        | k9_subset_1(u1_struct_0(esk4_0),esk5_0,X35) != k1_tarski(esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X16,X15)
        | r2_hidden(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ r2_hidden(X16,X15)
        | m1_subset_1(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ m1_subset_1(X16,X15)
        | v1_xboole_0(X16)
        | ~ v1_xboole_0(X15) )
      & ( ~ v1_xboole_0(X16)
        | m1_subset_1(X16,X15)
        | ~ v1_xboole_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X5] : k2_tarski(X5,X5) = k1_tarski(X5) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | m1_subset_1(k1_tarski(X19),k1_zfmisc_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v4_pre_topc(X1,esk4_0)
    | k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1) != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X26,X27,X28,X31] :
      ( ( m1_subset_1(esk2_3(X26,X27,X28),k1_zfmisc_1(u1_struct_0(X26)))
        | ~ r1_tarski(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( v4_pre_topc(esk2_3(X26,X27,X28),X26)
        | ~ r1_tarski(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( k9_subset_1(u1_struct_0(X26),X27,esk2_3(X26,X27,X28)) = X28
        | ~ r1_tarski(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk3_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( r1_tarski(esk3_2(X26,X27),X27)
        | v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v4_pre_topc(X31,X26)
        | k9_subset_1(u1_struct_0(X26),X27,X31) != esk3_2(X26,X27)
        | v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1) != k1_enumset1(esk6_0,esk6_0,esk6_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_36,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk2_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_27]),c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( X1 != k1_enumset1(esk6_0,esk6_0,esk6_0)
    | ~ v4_pre_topc(esk2_3(esk4_0,esk5_0,X1),esk4_0)
    | ~ m1_subset_1(esk2_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_22])])).

cnf(c_0_44,plain,
    ( v4_pre_topc(esk2_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(k1_enumset1(X2,X2,X2),k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_22]),c_0_42])).

fof(c_0_48,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | r1_tarski(X10,X8)
        | X9 != k1_zfmisc_1(X8) )
      & ( ~ r1_tarski(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k1_zfmisc_1(X8) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | ~ r1_tarski(esk1_2(X12,X13),X12)
        | X13 = k1_zfmisc_1(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(esk1_2(X12,X13),X12)
        | X13 = k1_zfmisc_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_49,negated_conjecture,
    ( X1 != k1_enumset1(esk6_0,esk6_0,esk6_0)
    | ~ m1_subset_1(esk2_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_37]),c_0_38]),c_0_22])])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k1_enumset1(esk6_0,esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk5_0))
    | r2_hidden(k1_enumset1(esk6_0,esk6_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( X1 != k1_enumset1(esk6_0,esk6_0,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_37]),c_0_38]),c_0_22])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k1_enumset1(esk6_0,esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk5_0))
    | r1_tarski(k1_enumset1(esk6_0,esk6_0,esk6_0),X1)
    | k1_zfmisc_1(esk5_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k1_enumset1(esk6_0,esk6_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_25])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_57]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.16/0.36  % Computer   : n007.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 11:56:51 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.37  # Version: 2.5pre002
% 0.16/0.37  # No SInE strategy applied
% 0.16/0.37  # Trying AutoSched0 for 299 seconds
% 0.23/0.41  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.23/0.41  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.23/0.41  #
% 0.23/0.41  # Preprocessing time       : 0.029 s
% 0.23/0.41  
% 0.23/0.41  # Proof found!
% 0.23/0.41  # SZS status Theorem
% 0.23/0.41  # SZS output start CNFRefutation
% 0.23/0.41  fof(t33_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 0.23/0.41  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.23/0.41  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.23/0.41  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.23/0.41  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.23/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.23/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.23/0.41  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.23/0.41  fof(d6_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 0.23/0.41  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.23/0.41  fof(c_0_10, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3))))))))))), inference(assume_negation,[status(cth)],[t33_tex_2])).
% 0.23/0.41  fof(c_0_11, plain, ![X18]:m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.23/0.41  fof(c_0_12, plain, ![X17]:k2_subset_1(X17)=X17, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.23/0.41  fof(c_0_13, plain, ![X23, X24, X25]:(~r2_hidden(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X25))|~v1_xboole_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.23/0.41  fof(c_0_14, negated_conjecture, ![X35]:(l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(v2_tex_2(esk5_0,esk4_0)&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(r2_hidden(esk6_0,esk5_0)&(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(esk4_0)))|(~v4_pre_topc(X35,esk4_0)|k9_subset_1(u1_struct_0(esk4_0),esk5_0,X35)!=k1_tarski(esk6_0)))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.23/0.41  fof(c_0_15, plain, ![X15, X16]:(((~m1_subset_1(X16,X15)|r2_hidden(X16,X15)|v1_xboole_0(X15))&(~r2_hidden(X16,X15)|m1_subset_1(X16,X15)|v1_xboole_0(X15)))&((~m1_subset_1(X16,X15)|v1_xboole_0(X16)|~v1_xboole_0(X15))&(~v1_xboole_0(X16)|m1_subset_1(X16,X15)|~v1_xboole_0(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.23/0.41  cnf(c_0_16, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.23/0.41  cnf(c_0_17, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.23/0.41  fof(c_0_18, plain, ![X5]:k2_tarski(X5,X5)=k1_tarski(X5), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.23/0.41  fof(c_0_19, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.23/0.41  fof(c_0_20, plain, ![X19, X20]:(~r2_hidden(X19,X20)|m1_subset_1(k1_tarski(X19),k1_zfmisc_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.23/0.41  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.23/0.41  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.23/0.41  cnf(c_0_23, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.23/0.41  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.23/0.41  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.23/0.41  cnf(c_0_26, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v4_pre_topc(X1,esk4_0)|k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1)!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.23/0.41  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.23/0.41  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.23/0.41  fof(c_0_29, plain, ![X26, X27, X28, X31]:(((m1_subset_1(esk2_3(X26,X27,X28),k1_zfmisc_1(u1_struct_0(X26)))|~r1_tarski(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&((v4_pre_topc(esk2_3(X26,X27,X28),X26)|~r1_tarski(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&(k9_subset_1(u1_struct_0(X26),X27,esk2_3(X26,X27,X28))=X28|~r1_tarski(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))))&((m1_subset_1(esk3_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))|v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&((r1_tarski(esk3_2(X26,X27),X27)|v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X26)))|(~v4_pre_topc(X31,X26)|k9_subset_1(u1_struct_0(X26),X27,X31)!=esk3_2(X26,X27))|v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).
% 0.23/0.41  cnf(c_0_30, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.23/0.41  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.23/0.41  cnf(c_0_32, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk6_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.23/0.41  cnf(c_0_33, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_25])).
% 0.23/0.41  cnf(c_0_34, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.23/0.41  cnf(c_0_35, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1)!=k1_enumset1(esk6_0,esk6_0,esk6_0)|~v4_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.23/0.41  cnf(c_0_36, plain, (k9_subset_1(u1_struct_0(X1),X2,esk2_3(X1,X2,X3))=X3|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.23/0.41  cnf(c_0_37, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.23/0.41  cnf(c_0_38, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.23/0.41  cnf(c_0_39, plain, (m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_27]), c_0_28])).
% 0.23/0.41  cnf(c_0_40, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.23/0.41  cnf(c_0_41, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.23/0.41  cnf(c_0_42, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.23/0.41  cnf(c_0_43, negated_conjecture, (X1!=k1_enumset1(esk6_0,esk6_0,esk6_0)|~v4_pre_topc(esk2_3(esk4_0,esk5_0,X1),esk4_0)|~m1_subset_1(esk2_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_22])])).
% 0.23/0.41  cnf(c_0_44, plain, (v4_pre_topc(esk2_3(X1,X2,X3),X1)|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.23/0.41  cnf(c_0_45, plain, (v1_xboole_0(k1_zfmisc_1(X1))|r2_hidden(k1_enumset1(X2,X2,X2),k1_zfmisc_1(X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_39])).
% 0.23/0.41  cnf(c_0_46, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.23/0.41  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_22]), c_0_42])).
% 0.23/0.41  fof(c_0_48, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|r1_tarski(X10,X8)|X9!=k1_zfmisc_1(X8))&(~r1_tarski(X11,X8)|r2_hidden(X11,X9)|X9!=k1_zfmisc_1(X8)))&((~r2_hidden(esk1_2(X12,X13),X13)|~r1_tarski(esk1_2(X12,X13),X12)|X13=k1_zfmisc_1(X12))&(r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(esk1_2(X12,X13),X12)|X13=k1_zfmisc_1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.23/0.41  cnf(c_0_49, negated_conjecture, (X1!=k1_enumset1(esk6_0,esk6_0,esk6_0)|~m1_subset_1(esk2_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_37]), c_0_38]), c_0_22])])).
% 0.23/0.41  cnf(c_0_50, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.23/0.41  cnf(c_0_51, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.23/0.41  cnf(c_0_52, negated_conjecture, (r2_hidden(k1_enumset1(esk6_0,esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.23/0.41  cnf(c_0_53, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.23/0.41  cnf(c_0_54, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk5_0))|r2_hidden(k1_enumset1(esk6_0,esk6_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_45, c_0_34])).
% 0.23/0.41  cnf(c_0_55, negated_conjecture, (X1!=k1_enumset1(esk6_0,esk6_0,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_37]), c_0_38]), c_0_22])])).
% 0.23/0.41  cnf(c_0_56, negated_conjecture, (m1_subset_1(k1_enumset1(esk6_0,esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_47])).
% 0.23/0.41  cnf(c_0_57, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk5_0))|r1_tarski(k1_enumset1(esk6_0,esk6_0,esk6_0),X1)|k1_zfmisc_1(esk5_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.23/0.41  cnf(c_0_58, negated_conjecture, (~r1_tarski(k1_enumset1(esk6_0,esk6_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.23/0.41  cnf(c_0_59, plain, (v1_xboole_0(X1)|~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_25])).
% 0.23/0.41  cnf(c_0_60, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_57]), c_0_58])).
% 0.23/0.41  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_42]), ['proof']).
% 0.23/0.41  # SZS output end CNFRefutation
% 0.23/0.41  # Proof object total steps             : 62
% 0.23/0.41  # Proof object clause steps            : 41
% 0.23/0.41  # Proof object formula steps           : 21
% 0.23/0.41  # Proof object conjectures             : 26
% 0.23/0.41  # Proof object clause conjectures      : 23
% 0.23/0.41  # Proof object formula conjectures     : 3
% 0.23/0.41  # Proof object initial clauses used    : 19
% 0.23/0.41  # Proof object initial formulas used   : 10
% 0.23/0.41  # Proof object generating inferences   : 19
% 0.23/0.41  # Proof object simplifying inferences  : 22
% 0.23/0.41  # Training examples: 0 positive, 0 negative
% 0.23/0.41  # Parsed axioms                        : 11
% 0.23/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.23/0.41  # Initial clauses                      : 27
% 0.23/0.41  # Removed in clause preprocessing      : 3
% 0.23/0.41  # Initial clauses in saturation        : 24
% 0.23/0.41  # Processed clauses                    : 183
% 0.23/0.41  # ...of these trivial                  : 0
% 0.23/0.41  # ...subsumed                          : 29
% 0.23/0.41  # ...remaining for further processing  : 154
% 0.23/0.41  # Other redundant clauses eliminated   : 0
% 0.23/0.41  # Clauses deleted for lack of memory   : 0
% 0.23/0.41  # Backward-subsumed                    : 6
% 0.23/0.41  # Backward-rewritten                   : 5
% 0.23/0.41  # Generated clauses                    : 453
% 0.23/0.41  # ...of the previous two non-trivial   : 419
% 0.23/0.41  # Contextual simplify-reflections      : 4
% 0.23/0.41  # Paramodulations                      : 429
% 0.23/0.41  # Factorizations                       : 8
% 0.23/0.41  # Equation resolutions                 : 15
% 0.23/0.41  # Propositional unsat checks           : 0
% 0.23/0.41  #    Propositional check models        : 0
% 0.23/0.41  #    Propositional check unsatisfiable : 0
% 0.23/0.41  #    Propositional clauses             : 0
% 0.23/0.41  #    Propositional clauses after purity: 0
% 0.23/0.41  #    Propositional unsat core size     : 0
% 0.23/0.41  #    Propositional preprocessing time  : 0.000
% 0.23/0.41  #    Propositional encoding time       : 0.000
% 0.23/0.41  #    Propositional solver time         : 0.000
% 0.23/0.41  #    Success case prop preproc time    : 0.000
% 0.23/0.41  #    Success case prop encoding time   : 0.000
% 0.23/0.41  #    Success case prop solver time     : 0.000
% 0.23/0.41  # Current number of processed clauses  : 142
% 0.23/0.41  #    Positive orientable unit clauses  : 12
% 0.23/0.41  #    Positive unorientable unit clauses: 0
% 0.23/0.41  #    Negative unit clauses             : 5
% 0.23/0.41  #    Non-unit-clauses                  : 125
% 0.23/0.41  # Current number of unprocessed clauses: 245
% 0.23/0.41  # ...number of literals in the above   : 993
% 0.23/0.41  # Current number of archived formulas  : 0
% 0.23/0.41  # Current number of archived clauses   : 15
% 0.23/0.41  # Clause-clause subsumption calls (NU) : 2016
% 0.23/0.41  # Rec. Clause-clause subsumption calls : 1062
% 0.23/0.41  # Non-unit clause-clause subsumptions  : 26
% 0.23/0.41  # Unit Clause-clause subsumption calls : 69
% 0.23/0.41  # Rewrite failures with RHS unbound    : 0
% 0.23/0.41  # BW rewrite match attempts            : 5
% 0.23/0.41  # BW rewrite match successes           : 2
% 0.23/0.41  # Condensation attempts                : 0
% 0.23/0.41  # Condensation successes               : 0
% 0.23/0.41  # Termbank termtop insertions          : 9873
% 0.23/0.42  
% 0.23/0.42  # -------------------------------------------------
% 0.23/0.42  # User time                : 0.045 s
% 0.23/0.42  # System time              : 0.006 s
% 0.23/0.42  # Total time               : 0.051 s
% 0.23/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
