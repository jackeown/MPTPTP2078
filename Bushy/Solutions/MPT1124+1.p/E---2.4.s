%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : pre_topc__t55_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:44 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  88 expanded)
%              Number of clauses        :   26 (  35 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  191 ( 370 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_pre_topc,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',t55_pre_topc)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',t2_subset)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',dt_m1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',d9_pre_topc)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',fc5_struct_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',d3_tarski)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',t4_subset)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t55_pre_topc.p',dt_k2_struct_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t55_pre_topc])).

fof(c_0_11,plain,(
    ! [X54,X55] :
      ( ~ m1_subset_1(X54,X55)
      | v1_xboole_0(X55)
      | r2_hidden(X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ~ m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X15] :
      ( ~ l1_struct_0(X15)
      | k2_struct_0(X15) = u1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_14,plain,(
    ! [X34] :
      ( ~ l1_pre_topc(X34)
      | l1_struct_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_15,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_pre_topc(X36,X35)
      | l1_pre_topc(X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_23,plain,(
    ! [X22,X23,X24,X26,X28] :
      ( ( r1_tarski(k2_struct_0(X23),k2_struct_0(X22))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk5_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X24,u1_pre_topc(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(esk5_3(X22,X23,X24),u1_pre_topc(X22))
        | ~ r2_hidden(X24,u1_pre_topc(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( X24 = k9_subset_1(u1_struct_0(X23),esk5_3(X22,X23,X24),k2_struct_0(X23))
        | ~ r2_hidden(X24,u1_pre_topc(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X26,u1_pre_topc(X22))
        | X24 != k9_subset_1(u1_struct_0(X23),X26,k2_struct_0(X23))
        | r2_hidden(X24,u1_pre_topc(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk6_2(X22,X23),k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r1_tarski(k2_struct_0(X23),k2_struct_0(X22))
        | m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( ~ r2_hidden(esk6_2(X22,X23),u1_pre_topc(X23))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X28,u1_pre_topc(X22))
        | esk6_2(X22,X23) != k9_subset_1(u1_struct_0(X23),X28,k2_struct_0(X23))
        | ~ r1_tarski(k2_struct_0(X23),k2_struct_0(X22))
        | m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk7_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))
        | r2_hidden(esk6_2(X22,X23),u1_pre_topc(X23))
        | ~ r1_tarski(k2_struct_0(X23),k2_struct_0(X22))
        | m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(esk7_2(X22,X23),u1_pre_topc(X22))
        | r2_hidden(esk6_2(X22,X23),u1_pre_topc(X23))
        | ~ r1_tarski(k2_struct_0(X23),k2_struct_0(X22))
        | m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( esk6_2(X22,X23) = k9_subset_1(u1_struct_0(X23),esk7_2(X22,X23),k2_struct_0(X23))
        | r2_hidden(esk6_2(X22,X23),u1_pre_topc(X23))
        | ~ r1_tarski(k2_struct_0(X23),k2_struct_0(X22))
        | m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_24,plain,(
    ! [X69] :
      ( v2_struct_0(X69)
      | ~ l1_struct_0(X69)
      | ~ v1_xboole_0(k2_struct_0(X69)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_25,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( u1_struct_0(X1) = k2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

fof(c_0_28,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( ~ r1_tarski(X16,X17)
        | ~ r2_hidden(X18,X16)
        | r2_hidden(X18,X17) )
      & ( r2_hidden(esk4_2(X19,X20),X19)
        | r1_tarski(X19,X20) )
      & ( ~ r2_hidden(esk4_2(X19,X20),X20)
        | r1_tarski(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk2_0))
    | r2_hidden(esk3_0,k2_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_33,plain,(
    ! [X58,X59,X60] :
      ( ~ r2_hidden(X58,X59)
      | ~ m1_subset_1(X59,k1_zfmisc_1(X60))
      | m1_subset_1(X58,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_34,plain,(
    ! [X30] :
      ( ~ l1_struct_0(X30)
      | m1_subset_1(k2_struct_0(X30),k1_zfmisc_1(u1_struct_0(X30))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_0,k2_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_struct_0(X2))
    | ~ r2_hidden(X1,k2_struct_0(X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_0,k2_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_27])])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ r2_hidden(X1,k2_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_0,k2_struct_0(X1))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(X1))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_21]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
