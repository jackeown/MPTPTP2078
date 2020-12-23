%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:43 EST 2020

% Result     : Theorem 0.35s
% Output     : CNFRefutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 154 expanded)
%              Number of clauses        :   38 (  60 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  240 ( 808 expanded)
%              Number of equality atoms :   33 ( 106 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   32 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(t32_tex_2,axiom,(
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
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k1_tarski(X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

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

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(c_0_12,negated_conjecture,(
    ! [X37] :
      ( l1_pre_topc(esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
      & v2_tex_2(esk5_0,esk4_0)
      & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
      & r2_hidden(esk6_0,esk5_0)
      & ( ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ v4_pre_topc(X37,esk4_0)
        | k9_subset_1(u1_struct_0(esk4_0),esk5_0,X37) != k1_tarski(esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_13,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X8,X9] : k2_enumset1(X8,X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_15,plain,(
    ! [X30,X31,X32] :
      ( ( m1_subset_1(esk3_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X30)))
        | ~ r2_hidden(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v2_tex_2(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( v3_pre_topc(esk3_3(X30,X31,X32),X30)
        | ~ r2_hidden(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v2_tex_2(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( k9_subset_1(u1_struct_0(X30),X31,esk3_3(X30,X31,X32)) = k1_tarski(X32)
        | ~ r2_hidden(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v2_tex_2(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_tex_2])])])])])).

cnf(c_0_16,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v4_pre_topc(X1,esk4_0)
    | k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1) != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X24,X25,X26,X29] :
      ( ( m1_subset_1(esk1_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))
        | ~ r1_tarski(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_tex_2(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X24) )
      & ( v4_pre_topc(esk1_3(X24,X25,X26),X24)
        | ~ r1_tarski(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_tex_2(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X24) )
      & ( k9_subset_1(u1_struct_0(X24),X25,esk1_3(X24,X25,X26)) = X26
        | ~ r1_tarski(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v2_tex_2(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk2_2(X24,X25),k1_zfmisc_1(u1_struct_0(X24)))
        | v2_tex_2(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X24) )
      & ( r1_tarski(esk2_2(X24,X25),X25)
        | v2_tex_2(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X24) )
      & ( ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ v4_pre_topc(X29,X24)
        | k9_subset_1(u1_struct_0(X24),X25,X29) != esk2_2(X24,X25)
        | v2_tex_2(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).

cnf(c_0_20,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk3_3(X1,X2,X3)) = k1_tarski(X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | m1_subset_1(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_22,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1) != k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( v4_pre_topc(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_25,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | m1_subset_1(k9_subset_1(X13,X14,X15),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_26,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk3_3(X1,X2,X3)) = k2_enumset1(X3,X3,X3,X3)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X3,X2)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_17]),c_0_18])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_29,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X16))
      | k9_subset_1(X16,X17,X18) = k3_xboole_0(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_30,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | k9_subset_1(X10,X11,X12) = k9_subset_1(X10,X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_31,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk1_3(esk4_0,X1,X2)) != k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)
    | ~ v2_tex_2(X1,esk4_0)
    | ~ m1_subset_1(esk1_3(esk4_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_32,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk3_3(X1,X2,X3)) = k2_enumset1(X3,X3,X3,X3)
    | ~ v2_tex_2(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_38,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(esk4_0,esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk5_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_24])])])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,plain,
    ( m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_43,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_38])).

cnf(c_0_44,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

fof(c_0_45,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_46,negated_conjecture,
    ( ~ m1_subset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33]),c_0_24]),c_0_34])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_34]),c_0_33]),c_0_24])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_49,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_50,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ v2_tex_2(X3,X4)
    | ~ l1_pre_topc(X4)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_subset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_34]),c_0_33]),c_0_24])])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_48]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:13:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.35/0.53  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.35/0.53  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.35/0.53  #
% 0.35/0.53  # Preprocessing time       : 0.028 s
% 0.35/0.53  
% 0.35/0.53  # Proof found!
% 0.35/0.53  # SZS status Theorem
% 0.35/0.53  # SZS output start CNFRefutation
% 0.35/0.53  fof(t33_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 0.35/0.53  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.35/0.53  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.35/0.53  fof(t32_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tex_2)).
% 0.35/0.53  fof(d6_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 0.35/0.53  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.35/0.53  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.35/0.53  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.35/0.53  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.35/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.35/0.53  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.35/0.53  fof(c_0_11, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3))))))))))), inference(assume_negation,[status(cth)],[t33_tex_2])).
% 0.35/0.53  fof(c_0_12, negated_conjecture, ![X37]:(l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(v2_tex_2(esk5_0,esk4_0)&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(r2_hidden(esk6_0,esk5_0)&(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk4_0)))|(~v4_pre_topc(X37,esk4_0)|k9_subset_1(u1_struct_0(esk4_0),esk5_0,X37)!=k1_tarski(esk6_0)))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.35/0.53  fof(c_0_13, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.35/0.53  fof(c_0_14, plain, ![X8, X9]:k2_enumset1(X8,X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.35/0.53  fof(c_0_15, plain, ![X30, X31, X32]:((m1_subset_1(esk3_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X30)))|~r2_hidden(X32,X31)|~m1_subset_1(X32,u1_struct_0(X30))|~v2_tex_2(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&((v3_pre_topc(esk3_3(X30,X31,X32),X30)|~r2_hidden(X32,X31)|~m1_subset_1(X32,u1_struct_0(X30))|~v2_tex_2(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&(k9_subset_1(u1_struct_0(X30),X31,esk3_3(X30,X31,X32))=k1_tarski(X32)|~r2_hidden(X32,X31)|~m1_subset_1(X32,u1_struct_0(X30))|~v2_tex_2(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_tex_2])])])])])).
% 0.35/0.53  cnf(c_0_16, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v4_pre_topc(X1,esk4_0)|k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1)!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.35/0.53  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.35/0.53  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.35/0.53  fof(c_0_19, plain, ![X24, X25, X26, X29]:(((m1_subset_1(esk1_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))|~r1_tarski(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|~v2_tex_2(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~l1_pre_topc(X24))&((v4_pre_topc(esk1_3(X24,X25,X26),X24)|~r1_tarski(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|~v2_tex_2(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~l1_pre_topc(X24))&(k9_subset_1(u1_struct_0(X24),X25,esk1_3(X24,X25,X26))=X26|~r1_tarski(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|~v2_tex_2(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~l1_pre_topc(X24))))&((m1_subset_1(esk2_2(X24,X25),k1_zfmisc_1(u1_struct_0(X24)))|v2_tex_2(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~l1_pre_topc(X24))&((r1_tarski(esk2_2(X24,X25),X25)|v2_tex_2(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~l1_pre_topc(X24))&(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X24)))|(~v4_pre_topc(X29,X24)|k9_subset_1(u1_struct_0(X24),X25,X29)!=esk2_2(X24,X25))|v2_tex_2(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|~l1_pre_topc(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).
% 0.35/0.53  cnf(c_0_20, plain, (k9_subset_1(u1_struct_0(X1),X2,esk3_3(X1,X2,X3))=k1_tarski(X3)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.35/0.53  fof(c_0_21, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|m1_subset_1(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.35/0.53  cnf(c_0_22, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1)!=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)|~v4_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.35/0.53  cnf(c_0_23, plain, (v4_pre_topc(esk1_3(X1,X2,X3),X1)|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.35/0.53  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.35/0.53  fof(c_0_25, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X13))|m1_subset_1(k9_subset_1(X13,X14,X15),k1_zfmisc_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.35/0.53  cnf(c_0_26, plain, (k9_subset_1(u1_struct_0(X1),X2,esk3_3(X1,X2,X3))=k2_enumset1(X3,X3,X3,X3)|~l1_pre_topc(X1)|~r2_hidden(X3,X2)|~v2_tex_2(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_17]), c_0_18])).
% 0.35/0.53  cnf(c_0_27, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.35/0.53  cnf(c_0_28, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.35/0.53  fof(c_0_29, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(X16))|k9_subset_1(X16,X17,X18)=k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.35/0.53  fof(c_0_30, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X10))|k9_subset_1(X10,X11,X12)=k9_subset_1(X10,X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.35/0.53  cnf(c_0_31, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk1_3(esk4_0,X1,X2))!=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)|~v2_tex_2(X1,esk4_0)|~m1_subset_1(esk1_3(esk4_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.35/0.53  cnf(c_0_32, plain, (k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3))=X3|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.35/0.53  cnf(c_0_33, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.35/0.53  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.35/0.53  cnf(c_0_35, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.35/0.53  cnf(c_0_36, plain, (k9_subset_1(u1_struct_0(X1),X2,esk3_3(X1,X2,X3))=k2_enumset1(X3,X3,X3,X3)|~v2_tex_2(X2,X1)|~l1_pre_topc(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_26, c_0_27])).
% 0.35/0.53  cnf(c_0_37, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~l1_pre_topc(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_28, c_0_27])).
% 0.35/0.53  cnf(c_0_38, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.35/0.53  cnf(c_0_39, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.35/0.53  cnf(c_0_40, negated_conjecture, (~m1_subset_1(esk1_3(esk4_0,esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk5_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_24])])])).
% 0.35/0.53  cnf(c_0_41, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.35/0.53  cnf(c_0_42, plain, (m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(u1_struct_0(X2)))|~v2_tex_2(X3,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.35/0.53  cnf(c_0_43, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_35, c_0_38])).
% 0.35/0.53  cnf(c_0_44, plain, (k9_subset_1(X1,X2,X3)=k3_xboole_0(X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.35/0.53  fof(c_0_45, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.35/0.53  cnf(c_0_46, negated_conjecture, (~m1_subset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_33]), c_0_24]), c_0_34])])).
% 0.35/0.53  cnf(c_0_47, negated_conjecture, (m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_34]), c_0_33]), c_0_24])])).
% 0.35/0.53  cnf(c_0_48, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.35/0.53  fof(c_0_49, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.35/0.53  cnf(c_0_50, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.35/0.53  cnf(c_0_51, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.35/0.53  cnf(c_0_52, negated_conjecture, (~r1_tarski(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.35/0.53  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.35/0.53  cnf(c_0_54, plain, (m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(X2))|~v2_tex_2(X3,X4)|~l1_pre_topc(X4)|~r2_hidden(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_50, c_0_36])).
% 0.35/0.53  cnf(c_0_55, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.35/0.53  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_51])).
% 0.35/0.53  cnf(c_0_57, negated_conjecture, (~m1_subset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.35/0.53  cnf(c_0_58, negated_conjecture, (m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,esk5_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_34]), c_0_33]), c_0_24])])).
% 0.35/0.53  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.35/0.53  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_48]), c_0_59])]), ['proof']).
% 0.35/0.53  # SZS output end CNFRefutation
% 0.35/0.53  # Proof object total steps             : 61
% 0.35/0.53  # Proof object clause steps            : 38
% 0.35/0.53  # Proof object formula steps           : 23
% 0.35/0.53  # Proof object conjectures             : 17
% 0.35/0.53  # Proof object clause conjectures      : 14
% 0.35/0.53  # Proof object formula conjectures     : 3
% 0.35/0.53  # Proof object initial clauses used    : 19
% 0.35/0.53  # Proof object initial formulas used   : 11
% 0.35/0.53  # Proof object generating inferences   : 14
% 0.35/0.53  # Proof object simplifying inferences  : 30
% 0.35/0.53  # Training examples: 0 positive, 0 negative
% 0.35/0.53  # Parsed axioms                        : 11
% 0.35/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.35/0.53  # Initial clauses                      : 26
% 0.35/0.53  # Removed in clause preprocessing      : 2
% 0.35/0.53  # Initial clauses in saturation        : 24
% 0.35/0.53  # Processed clauses                    : 1518
% 0.35/0.53  # ...of these trivial                  : 2
% 0.35/0.53  # ...subsumed                          : 1275
% 0.35/0.53  # ...remaining for further processing  : 241
% 0.35/0.53  # Other redundant clauses eliminated   : 7
% 0.35/0.53  # Clauses deleted for lack of memory   : 0
% 0.35/0.53  # Backward-subsumed                    : 7
% 0.35/0.53  # Backward-rewritten                   : 0
% 0.35/0.53  # Generated clauses                    : 10638
% 0.35/0.53  # ...of the previous two non-trivial   : 10425
% 0.35/0.53  # Contextual simplify-reflections      : 9
% 0.35/0.53  # Paramodulations                      : 10631
% 0.35/0.53  # Factorizations                       : 0
% 0.35/0.53  # Equation resolutions                 : 7
% 0.35/0.53  # Propositional unsat checks           : 0
% 0.35/0.53  #    Propositional check models        : 0
% 0.35/0.53  #    Propositional check unsatisfiable : 0
% 0.35/0.53  #    Propositional clauses             : 0
% 0.35/0.53  #    Propositional clauses after purity: 0
% 0.35/0.53  #    Propositional unsat core size     : 0
% 0.35/0.53  #    Propositional preprocessing time  : 0.000
% 0.35/0.53  #    Propositional encoding time       : 0.000
% 0.35/0.53  #    Propositional solver time         : 0.000
% 0.35/0.53  #    Success case prop preproc time    : 0.000
% 0.35/0.53  #    Success case prop encoding time   : 0.000
% 0.35/0.53  #    Success case prop solver time     : 0.000
% 0.35/0.53  # Current number of processed clauses  : 232
% 0.35/0.53  #    Positive orientable unit clauses  : 13
% 0.35/0.53  #    Positive unorientable unit clauses: 0
% 0.35/0.53  #    Negative unit clauses             : 2
% 0.35/0.53  #    Non-unit-clauses                  : 217
% 0.35/0.53  # Current number of unprocessed clauses: 8878
% 0.35/0.53  # ...number of literals in the above   : 44052
% 0.35/0.53  # Current number of archived formulas  : 0
% 0.35/0.53  # Current number of archived clauses   : 9
% 0.35/0.53  # Clause-clause subsumption calls (NU) : 39010
% 0.35/0.53  # Rec. Clause-clause subsumption calls : 22146
% 0.35/0.53  # Non-unit clause-clause subsumptions  : 1291
% 0.35/0.53  # Unit Clause-clause subsumption calls : 19
% 0.35/0.53  # Rewrite failures with RHS unbound    : 0
% 0.35/0.53  # BW rewrite match attempts            : 10
% 0.35/0.53  # BW rewrite match successes           : 0
% 0.35/0.53  # Condensation attempts                : 0
% 0.35/0.53  # Condensation successes               : 0
% 0.35/0.53  # Termbank termtop insertions          : 250330
% 0.35/0.53  
% 0.35/0.53  # -------------------------------------------------
% 0.35/0.53  # User time                : 0.183 s
% 0.35/0.53  # System time              : 0.011 s
% 0.35/0.53  # Total time               : 0.194 s
% 0.35/0.53  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
