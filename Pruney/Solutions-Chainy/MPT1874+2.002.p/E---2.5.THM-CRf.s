%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:02 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 126 expanded)
%              Number of clauses        :   41 (  51 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  207 ( 498 expanded)
%              Number of equality atoms :   26 (  62 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t42_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,X2)
                 => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t41_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r1_tarski(X3,X2)
                 => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(c_0_14,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | m1_subset_1(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_15,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_16,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X25,X26)
      | v1_xboole_0(X26)
      | r2_hidden(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_17,plain,(
    ! [X20] : ~ v1_xboole_0(k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tex_2(X2,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( r2_hidden(X3,X2)
                   => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_tex_2])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(pm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_20,c_0_19]),c_0_21])).

fof(c_0_25,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | r1_tarski(k1_zfmisc_1(X18),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & v2_tex_2(esk5_0,esk4_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & r2_hidden(esk6_0,esk5_0)
    & k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) != k6_domain_1(u1_struct_0(esk4_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

fof(c_0_27,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v2_tex_2(X35,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ r1_tarski(X36,X35)
        | k9_subset_1(u1_struct_0(X34),X35,k2_pre_topc(X34,X36)) = X36
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk3_2(X34,X35),k1_zfmisc_1(u1_struct_0(X34)))
        | v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( r1_tarski(esk3_2(X34,X35),X35)
        | v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( k9_subset_1(u1_struct_0(X34),X35,k2_pre_topc(X34,esk3_2(X34,X35))) != esk3_2(X34,X35)
        | v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X3),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(pm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) != k6_domain_1(u1_struct_0(esk4_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k9_subset_1(u1_struct_0(X2),X1,k2_pre_topc(X2,X3)) = X3
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(pm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_39,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | m1_subset_1(k1_tarski(X21),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_40,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_41,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_42,negated_conjecture,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(pm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X32,X33] :
      ( v1_xboole_0(X32)
      | ~ m1_subset_1(X33,X32)
      | k6_domain_1(X32,X33) = k1_tarski(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_49,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0) ),
    inference(pm,[status(thm)],[c_0_42,c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(pm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_52,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X13,X12)
        | r1_tarski(X13,X11)
        | X12 != k1_zfmisc_1(X11) )
      & ( ~ r1_tarski(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k1_zfmisc_1(X11) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | ~ r1_tarski(esk2_2(X15,X16),X15)
        | X16 = k1_zfmisc_1(X15) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(esk2_2(X15,X16),X15)
        | X16 = k1_zfmisc_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_53,plain,
    ( m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_55,plain,(
    ! [X23,X24] :
      ( ~ v1_xboole_0(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | v1_xboole_0(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_56,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0) ),
    inference(pm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( r2_hidden(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_20,c_0_53]),c_0_21])).

cnf(c_0_61,plain,
    ( k6_domain_1(X1,X2) = k1_enumset1(X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_46]),c_0_47])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(pm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( X1 != k1_zfmisc_1(esk5_0)
    | ~ r2_hidden(k6_domain_1(u1_struct_0(esk4_0),esk6_0),X1) ),
    inference(pm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( r2_hidden(k6_domain_1(X1,X2),k1_zfmisc_1(X3))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(pm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_35]),c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k1_zfmisc_1(X1) != k1_zfmisc_1(esk5_0)
    | ~ r2_hidden(esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_64,c_0_65]),c_0_66])]),c_0_67])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(pm,[status(thm)],[c_0_68,c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:07:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.19/0.48  # and selection function NoSelection.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.028 s
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.48  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.48  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.48  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.48  fof(t42_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 0.19/0.48  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.19/0.48  fof(t41_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 0.19/0.48  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.19/0.48  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.48  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.48  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.48  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.48  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.48  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.48  fof(c_0_14, plain, ![X29, X30, X31]:(~r2_hidden(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(X31))|m1_subset_1(X29,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.48  fof(c_0_15, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.48  fof(c_0_16, plain, ![X25, X26]:(~m1_subset_1(X25,X26)|(v1_xboole_0(X26)|r2_hidden(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.48  fof(c_0_17, plain, ![X20]:~v1_xboole_0(k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.48  cnf(c_0_18, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.48  cnf(c_0_19, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_20, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_21, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.48  fof(c_0_22, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=k6_domain_1(u1_struct_0(X1),X3))))))), inference(assume_negation,[status(cth)],[t42_tex_2])).
% 0.19/0.48  cnf(c_0_23, plain, (m1_subset_1(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(pm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.48  cnf(c_0_24, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_20, c_0_19]), c_0_21])).
% 0.19/0.48  fof(c_0_25, plain, ![X18, X19]:(~r1_tarski(X18,X19)|r1_tarski(k1_zfmisc_1(X18),k1_zfmisc_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.19/0.48  fof(c_0_26, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(v2_tex_2(esk5_0,esk4_0)&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(r2_hidden(esk6_0,esk5_0)&k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))!=k6_domain_1(u1_struct_0(esk4_0),esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.19/0.48  fof(c_0_27, plain, ![X34, X35, X36]:((~v2_tex_2(X35,X34)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|(~r1_tarski(X36,X35)|k9_subset_1(u1_struct_0(X34),X35,k2_pre_topc(X34,X36))=X36))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&((m1_subset_1(esk3_2(X34,X35),k1_zfmisc_1(u1_struct_0(X34)))|v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&((r1_tarski(esk3_2(X34,X35),X35)|v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(k9_subset_1(u1_struct_0(X34),X35,k2_pre_topc(X34,esk3_2(X34,X35)))!=esk3_2(X34,X35)|v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).
% 0.19/0.48  cnf(c_0_28, plain, (m1_subset_1(X1,X2)|~r1_tarski(k1_zfmisc_1(X3),X2)|~r1_tarski(X1,X3)), inference(pm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.48  cnf(c_0_29, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.48  cnf(c_0_30, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))!=k6_domain_1(u1_struct_0(esk4_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_31, plain, (k9_subset_1(u1_struct_0(X2),X1,k2_pre_topc(X2,X3))=X3|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.48  cnf(c_0_32, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(pm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.48  fof(c_0_39, plain, ![X21, X22]:(~r2_hidden(X21,X22)|m1_subset_1(k1_tarski(X21),k1_zfmisc_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.19/0.48  fof(c_0_40, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.48  fof(c_0_41, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.48  cnf(c_0_42, negated_conjecture, (~m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.19/0.48  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(pm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.48  cnf(c_0_44, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk4_0))), inference(pm,[status(thm)],[c_0_37, c_0_35])).
% 0.19/0.48  cnf(c_0_45, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.48  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.48  cnf(c_0_47, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.48  fof(c_0_48, plain, ![X32, X33]:(v1_xboole_0(X32)|~m1_subset_1(X33,X32)|k6_domain_1(X32,X33)=k1_tarski(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.48  fof(c_0_49, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.48  cnf(c_0_50, negated_conjecture, (~r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|~r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0)), inference(pm,[status(thm)],[c_0_42, c_0_19])).
% 0.19/0.48  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk4_0))|~r1_tarski(X1,esk5_0)), inference(pm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.48  fof(c_0_52, plain, ![X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X13,X12)|r1_tarski(X13,X11)|X12!=k1_zfmisc_1(X11))&(~r1_tarski(X14,X11)|r2_hidden(X14,X12)|X12!=k1_zfmisc_1(X11)))&((~r2_hidden(esk2_2(X15,X16),X16)|~r1_tarski(esk2_2(X15,X16),X15)|X16=k1_zfmisc_1(X15))&(r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(esk2_2(X15,X16),X15)|X16=k1_zfmisc_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.48  cnf(c_0_53, plain, (m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.19/0.48  cnf(c_0_54, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.48  fof(c_0_55, plain, ![X23, X24]:(~v1_xboole_0(X23)|(~m1_subset_1(X24,k1_zfmisc_1(X23))|v1_xboole_0(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.48  cnf(c_0_56, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.48  cnf(c_0_57, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_58, negated_conjecture, (~r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0)), inference(pm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.48  cnf(c_0_59, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.48  cnf(c_0_60, plain, (r2_hidden(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_20, c_0_53]), c_0_21])).
% 0.19/0.48  cnf(c_0_61, plain, (k6_domain_1(X1,X2)=k1_enumset1(X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_46]), c_0_47])).
% 0.19/0.48  cnf(c_0_62, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.48  cnf(c_0_63, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(pm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.48  cnf(c_0_64, negated_conjecture, (X1!=k1_zfmisc_1(esk5_0)|~r2_hidden(k6_domain_1(u1_struct_0(esk4_0),esk6_0),X1)), inference(pm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.48  cnf(c_0_65, plain, (r2_hidden(k6_domain_1(X1,X2),k1_zfmisc_1(X3))|v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~r2_hidden(X2,X3)), inference(pm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.48  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_67, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_35]), c_0_63])).
% 0.19/0.48  cnf(c_0_68, negated_conjecture, (k1_zfmisc_1(X1)!=k1_zfmisc_1(esk5_0)|~r2_hidden(esk6_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_64, c_0_65]), c_0_66])]), c_0_67])).
% 0.19/0.48  cnf(c_0_69, negated_conjecture, ($false), inference(pm,[status(thm)],[c_0_68, c_0_57]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 70
% 0.19/0.48  # Proof object clause steps            : 41
% 0.19/0.48  # Proof object formula steps           : 29
% 0.19/0.48  # Proof object conjectures             : 21
% 0.19/0.48  # Proof object clause conjectures      : 18
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 22
% 0.19/0.48  # Proof object initial formulas used   : 14
% 0.19/0.48  # Proof object generating inferences   : 17
% 0.19/0.48  # Proof object simplifying inferences  : 16
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 14
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 29
% 0.19/0.48  # Removed in clause preprocessing      : 2
% 0.19/0.48  # Initial clauses in saturation        : 27
% 0.19/0.48  # Processed clauses                    : 714
% 0.19/0.48  # ...of these trivial                  : 1
% 0.19/0.48  # ...subsumed                          : 325
% 0.19/0.48  # ...remaining for further processing  : 388
% 0.19/0.48  # Other redundant clauses eliminated   : 0
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 16
% 0.19/0.48  # Backward-rewritten                   : 0
% 0.19/0.48  # Generated clauses                    : 6173
% 0.19/0.48  # ...of the previous two non-trivial   : 6084
% 0.19/0.48  # Contextual simplify-reflections      : 0
% 0.19/0.48  # Paramodulations                      : 6139
% 0.19/0.48  # Factorizations                       : 6
% 0.19/0.48  # Equation resolutions                 : 28
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 372
% 0.19/0.48  #    Positive orientable unit clauses  : 33
% 0.19/0.48  #    Positive unorientable unit clauses: 0
% 0.19/0.48  #    Negative unit clauses             : 9
% 0.19/0.48  #    Non-unit-clauses                  : 330
% 0.19/0.48  # Current number of unprocessed clauses: 5382
% 0.19/0.48  # ...number of literals in the above   : 20705
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 18
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 2714
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 1520
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 261
% 0.19/0.48  # Unit Clause-clause subsumption calls : 205
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 91
% 0.19/0.48  # BW rewrite match successes           : 0
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 59001
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.136 s
% 0.19/0.48  # System time              : 0.009 s
% 0.19/0.48  # Total time               : 0.145 s
% 0.19/0.48  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
