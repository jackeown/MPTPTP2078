%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 119 expanded)
%              Number of clauses        :   31 (  45 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  186 ( 614 expanded)
%              Number of equality atoms :   24 (  81 expanded)
%              Maximal formula depth    :   16 (   5 average)
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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

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

fof(c_0_11,negated_conjecture,(
    ! [X43] :
      ( l1_pre_topc(esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
      & v2_tex_2(esk6_0,esk5_0)
      & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
      & r2_hidden(esk7_0,esk6_0)
      & ( ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(esk5_0)))
        | ~ v4_pre_topc(X43,esk5_0)
        | k9_subset_1(u1_struct_0(esk5_0),esk6_0,X43) != k1_tarski(esk7_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_12,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_15,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v4_pre_topc(X1,esk5_0)
    | k9_subset_1(u1_struct_0(esk5_0),esk6_0,X1) != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X34,X35,X36,X39] :
      ( ( m1_subset_1(esk3_3(X34,X35,X36),k1_zfmisc_1(u1_struct_0(X34)))
        | ~ r1_tarski(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( v4_pre_topc(esk3_3(X34,X35,X36),X34)
        | ~ r1_tarski(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( k9_subset_1(u1_struct_0(X34),X35,esk3_3(X34,X35,X36)) = X36
        | ~ r1_tarski(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk4_2(X34,X35),k1_zfmisc_1(u1_struct_0(X34)))
        | v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( r1_tarski(esk4_2(X34,X35),X35)
        | v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ v4_pre_topc(X39,X34)
        | k9_subset_1(u1_struct_0(X34),X35,X39) != esk4_2(X34,X35)
        | v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).

cnf(c_0_20,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk6_0,X1) != k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)
    | ~ v4_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_21,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk3_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_25,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | r1_tarski(X17,X15)
        | X16 != k1_zfmisc_1(X15) )
      & ( ~ r1_tarski(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k1_zfmisc_1(X15) )
      & ( ~ r2_hidden(esk2_2(X19,X20),X20)
        | ~ r1_tarski(esk2_2(X19,X20),X19)
        | X20 = k1_zfmisc_1(X19) )
      & ( r2_hidden(esk2_2(X19,X20),X20)
        | r1_tarski(esk2_2(X19,X20),X19)
        | X20 = k1_zfmisc_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_26,plain,(
    ! [X22,X23,X24] :
      ( ( r2_hidden(X22,X24)
        | ~ r1_tarski(k2_tarski(X22,X23),X24) )
      & ( r2_hidden(X23,X24)
        | ~ r1_tarski(k2_tarski(X22,X23),X24) )
      & ( ~ r2_hidden(X22,X24)
        | ~ r2_hidden(X23,X24)
        | r1_tarski(k2_tarski(X22,X23),X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_27,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | ~ v1_xboole_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_28,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v4_pre_topc(esk3_3(esk5_0,esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)),esk5_0)
    | ~ m1_subset_1(esk3_3(esk5_0,esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),esk6_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24])])])).

cnf(c_0_30,plain,
    ( v4_pre_topc(esk3_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( ~ m1_subset_1(esk3_3(esk5_0,esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_38,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | m1_subset_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_17]),c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( ~ m1_subset_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( r2_hidden(k2_enumset1(X1,X1,X1,X2),k1_zfmisc_1(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( ~ m1_subset_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_44])])).

cnf(c_0_49,plain,
    ( m1_subset_1(k2_enumset1(X1,X1,X1,X2),k1_zfmisc_1(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:55:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t33_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.37  fof(d6_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 0.19/0.37  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.37  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.19/0.37  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.37  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.37  fof(c_0_10, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3))))))))))), inference(assume_negation,[status(cth)],[t33_tex_2])).
% 0.19/0.37  fof(c_0_11, negated_conjecture, ![X43]:(l1_pre_topc(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(v2_tex_2(esk6_0,esk5_0)&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&(r2_hidden(esk7_0,esk6_0)&(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(esk5_0)))|(~v4_pre_topc(X43,esk5_0)|k9_subset_1(u1_struct_0(esk5_0),esk6_0,X43)!=k1_tarski(esk7_0)))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.19/0.37  fof(c_0_12, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  fof(c_0_13, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.37  fof(c_0_14, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v4_pre_topc(X1,esk5_0)|k9_subset_1(u1_struct_0(esk5_0),esk6_0,X1)!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  fof(c_0_19, plain, ![X34, X35, X36, X39]:(((m1_subset_1(esk3_3(X34,X35,X36),k1_zfmisc_1(u1_struct_0(X34)))|~r1_tarski(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))&((v4_pre_topc(esk3_3(X34,X35,X36),X34)|~r1_tarski(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))&(k9_subset_1(u1_struct_0(X34),X35,esk3_3(X34,X35,X36))=X36|~r1_tarski(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))))&((m1_subset_1(esk4_2(X34,X35),k1_zfmisc_1(u1_struct_0(X34)))|v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))&((r1_tarski(esk4_2(X34,X35),X35)|v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))&(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X34)))|(~v4_pre_topc(X39,X34)|k9_subset_1(u1_struct_0(X34),X35,X39)!=esk4_2(X34,X35))|v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk6_0,X1)!=k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)|~v4_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.37  cnf(c_0_21, plain, (k9_subset_1(u1_struct_0(X1),X2,esk3_3(X1,X2,X3))=X3|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (v2_tex_2(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  fof(c_0_25, plain, ![X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X17,X16)|r1_tarski(X17,X15)|X16!=k1_zfmisc_1(X15))&(~r1_tarski(X18,X15)|r2_hidden(X18,X16)|X16!=k1_zfmisc_1(X15)))&((~r2_hidden(esk2_2(X19,X20),X20)|~r1_tarski(esk2_2(X19,X20),X19)|X20=k1_zfmisc_1(X19))&(r2_hidden(esk2_2(X19,X20),X20)|r1_tarski(esk2_2(X19,X20),X19)|X20=k1_zfmisc_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.37  fof(c_0_26, plain, ![X22, X23, X24]:(((r2_hidden(X22,X24)|~r1_tarski(k2_tarski(X22,X23),X24))&(r2_hidden(X23,X24)|~r1_tarski(k2_tarski(X22,X23),X24)))&(~r2_hidden(X22,X24)|~r2_hidden(X23,X24)|r1_tarski(k2_tarski(X22,X23),X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.19/0.37  fof(c_0_27, plain, ![X29, X30, X31]:(~r2_hidden(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(X31))|~v1_xboole_0(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.37  fof(c_0_28, plain, ![X27, X28]:(~m1_subset_1(X27,X28)|(v1_xboole_0(X28)|r2_hidden(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (~v4_pre_topc(esk3_3(esk5_0,esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)),esk5_0)|~m1_subset_1(esk3_3(esk5_0,esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),esk6_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24])])])).
% 0.19/0.37  cnf(c_0_30, plain, (v4_pre_topc(esk3_3(X1,X2,X3),X1)|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_31, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_32, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_33, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_34, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (~m1_subset_1(esk3_3(esk5_0,esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_22]), c_0_23]), c_0_24])])).
% 0.19/0.37  cnf(c_0_37, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  fof(c_0_38, plain, ![X25, X26]:(~r2_hidden(X25,X26)|m1_subset_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.37  cnf(c_0_39, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_31])).
% 0.19/0.37  cnf(c_0_40, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_17]), c_0_18])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (~r2_hidden(X1,esk6_0)|~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_33, c_0_24])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (~m1_subset_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_22]), c_0_23]), c_0_24])])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_45, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.37  cnf(c_0_46, plain, (r2_hidden(k2_enumset1(X1,X1,X1,X2),k1_zfmisc_1(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (~m1_subset_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_44])])).
% 0.19/0.37  cnf(c_0_49, plain, (m1_subset_1(k2_enumset1(X1,X1,X1,X2),k1_zfmisc_1(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.37  cnf(c_0_50, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_47, c_0_44])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 52
% 0.19/0.37  # Proof object clause steps            : 31
% 0.19/0.37  # Proof object formula steps           : 21
% 0.19/0.37  # Proof object conjectures             : 19
% 0.19/0.37  # Proof object clause conjectures      : 16
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 17
% 0.19/0.37  # Proof object initial formulas used   : 10
% 0.19/0.37  # Proof object generating inferences   : 11
% 0.19/0.37  # Proof object simplifying inferences  : 23
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 12
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 28
% 0.19/0.37  # Removed in clause preprocessing      : 3
% 0.19/0.37  # Initial clauses in saturation        : 25
% 0.19/0.37  # Processed clauses                    : 119
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 30
% 0.19/0.37  # ...remaining for further processing  : 89
% 0.19/0.37  # Other redundant clauses eliminated   : 4
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 9
% 0.19/0.37  # Backward-rewritten                   : 7
% 0.19/0.37  # Generated clauses                    : 206
% 0.19/0.37  # ...of the previous two non-trivial   : 186
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 198
% 0.19/0.37  # Factorizations                       : 4
% 0.19/0.37  # Equation resolutions                 : 4
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 71
% 0.19/0.37  #    Positive orientable unit clauses  : 8
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 4
% 0.19/0.37  #    Non-unit-clauses                  : 59
% 0.19/0.37  # Current number of unprocessed clauses: 79
% 0.19/0.37  # ...number of literals in the above   : 399
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 19
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 1019
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 427
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 38
% 0.19/0.37  # Unit Clause-clause subsumption calls : 12
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 2
% 0.19/0.37  # BW rewrite match successes           : 2
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 5613
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.033 s
% 0.19/0.37  # System time              : 0.008 s
% 0.19/0.37  # Total time               : 0.041 s
% 0.19/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
