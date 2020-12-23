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
% DateTime   : Thu Dec  3 11:18:42 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 130 expanded)
%              Number of clauses        :   44 (  59 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  229 ( 409 expanded)
%              Number of equality atoms :   82 ( 113 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t1_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t43_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(c_0_15,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_16,plain,(
    ! [X26,X27] : r1_tarski(X26,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_17,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | ~ r1_tarski(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_18,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_zfmisc_1(X2) )
           => ( r1_tarski(X1,X2)
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t1_tex_2])).

fof(c_0_22,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | r1_tarski(X12,k2_xboole_0(X14,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,k2_xboole_0(X22,X23))
      | r1_tarski(k4_xboole_0(X21,X22),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & v1_zfmisc_1(esk4_0)
    & r1_tarski(esk3_0,esk4_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_30,plain,(
    ! [X20] : r1_tarski(k1_xboole_0,X20) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,esk1_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_28])).

fof(c_0_36,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_37,plain,(
    ! [X30,X31,X32] :
      ( ( X31 = k1_tarski(X30)
        | X31 = k1_xboole_0
        | X31 = k1_tarski(X30)
        | k1_tarski(X30) != k2_xboole_0(X31,X32) )
      & ( X32 = k1_xboole_0
        | X31 = k1_xboole_0
        | X31 = k1_tarski(X30)
        | k1_tarski(X30) != k2_xboole_0(X31,X32) )
      & ( X31 = k1_tarski(X30)
        | X32 = k1_tarski(X30)
        | X31 = k1_tarski(X30)
        | k1_tarski(X30) != k2_xboole_0(X31,X32) )
      & ( X32 = k1_xboole_0
        | X32 = k1_tarski(X30)
        | X31 = k1_tarski(X30)
        | k1_tarski(X30) != k2_xboole_0(X31,X32) )
      & ( X31 = k1_tarski(X30)
        | X31 = k1_xboole_0
        | X32 = k1_tarski(X30)
        | k1_tarski(X30) != k2_xboole_0(X31,X32) )
      & ( X32 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_tarski(X30)
        | k1_tarski(X30) != k2_xboole_0(X31,X32) )
      & ( X31 = k1_tarski(X30)
        | X32 = k1_tarski(X30)
        | X32 = k1_tarski(X30)
        | k1_tarski(X30) != k2_xboole_0(X31,X32) )
      & ( X32 = k1_xboole_0
        | X32 = k1_tarski(X30)
        | X32 = k1_tarski(X30)
        | k1_tarski(X30) != k2_xboole_0(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_zfmisc_1])])])).

fof(c_0_38,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X25)
      | ~ r1_tarski(X25,X24)
      | ~ r1_xboole_0(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_39,plain,(
    ! [X28,X29] :
      ( ( ~ r1_xboole_0(X28,X29)
        | k4_xboole_0(X28,X29) = X28 )
      & ( k4_xboole_0(X28,X29) != X28
        | r1_xboole_0(X28,X29) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,esk1_2(k4_xboole_0(X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | k1_tarski(X2) != k2_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_47,plain,(
    ! [X35,X36] :
      ( v1_xboole_0(X35)
      | ~ m1_subset_1(X36,X35)
      | k6_domain_1(X35,X36) = k1_tarski(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_48,plain,(
    ! [X37,X39] :
      ( ( m1_subset_1(esk2_1(X37),X37)
        | ~ v1_zfmisc_1(X37)
        | v1_xboole_0(X37) )
      & ( X37 = k6_domain_1(X37,esk2_1(X37))
        | ~ v1_zfmisc_1(X37)
        | v1_xboole_0(X37) )
      & ( ~ m1_subset_1(X39,X37)
        | X37 != k6_domain_1(X37,X39)
        | v1_zfmisc_1(X37)
        | v1_xboole_0(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),X2)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(esk4_0,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | k1_tarski(X2) != k2_xboole_0(X1,X3) ),
    inference(cn,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( m1_subset_1(esk2_1(X1),X1)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X1)
    | k4_xboole_0(X1,X2) != X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk3_0,X1) = k1_xboole_0
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_41])).

cnf(c_0_61,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_45])])).

cnf(c_0_62,plain,
    ( X1 = k6_domain_1(X1,esk2_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,plain,
    ( k6_domain_1(X1,esk2_1(X1)) = k1_tarski(esk2_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r1_tarski(esk4_0,X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( esk3_0 = k1_tarski(X1)
    | esk3_0 = k1_xboole_0
    | ~ r1_tarski(esk4_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_66,plain,
    ( k1_tarski(esk2_1(X1)) = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_20])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( esk3_0 = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( v1_zfmisc_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_72,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])]),c_0_72]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:26:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.40  # AutoSched0-Mode selected heuristic G_E___208_C12_11_nc_F1_SE_CS_SP_PS_S063N
% 0.12/0.40  # and selection function SelectMaxLComplexAvoidPosUPred.
% 0.12/0.40  #
% 0.12/0.40  # Preprocessing time       : 0.028 s
% 0.12/0.40  # Presaturation interreduction done
% 0.12/0.40  
% 0.12/0.40  # Proof found!
% 0.12/0.40  # SZS status Theorem
% 0.12/0.40  # SZS output start CNFRefutation
% 0.12/0.40  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.12/0.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.12/0.40  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.40  fof(t1_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 0.12/0.40  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.12/0.40  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.12/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.40  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.12/0.40  fof(t43_zfmisc_1, axiom, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.12/0.40  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.12/0.40  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.12/0.40  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.12/0.40  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 0.12/0.40  fof(c_0_15, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_tarski(X18,X19)|r1_tarski(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.12/0.40  fof(c_0_16, plain, ![X26, X27]:r1_tarski(X26,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.12/0.40  fof(c_0_17, plain, ![X33, X34]:(~r2_hidden(X33,X34)|~r1_tarski(X34,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.40  fof(c_0_18, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.40  cnf(c_0_19, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  cnf(c_0_20, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.40  fof(c_0_21, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2)))), inference(assume_negation,[status(cth)],[t1_tex_2])).
% 0.12/0.40  fof(c_0_22, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|r1_tarski(X12,k2_xboole_0(X14,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.12/0.40  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.40  cnf(c_0_24, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.40  fof(c_0_25, plain, ![X21, X22, X23]:(~r1_tarski(X21,k2_xboole_0(X22,X23))|r1_tarski(k4_xboole_0(X21,X22),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.12/0.40  cnf(c_0_26, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.40  fof(c_0_27, negated_conjecture, (~v1_xboole_0(esk3_0)&((~v1_xboole_0(esk4_0)&v1_zfmisc_1(esk4_0))&(r1_tarski(esk3_0,esk4_0)&esk3_0!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.12/0.40  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.40  fof(c_0_29, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.40  fof(c_0_30, plain, ![X20]:r1_tarski(k1_xboole_0,X20), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.40  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,esk1_2(X1,X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.40  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.40  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_19, c_0_26])).
% 0.12/0.40  cnf(c_0_34, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_19, c_0_28])).
% 0.12/0.40  fof(c_0_36, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.12/0.40  fof(c_0_37, plain, ![X30, X31, X32]:((((X31=k1_tarski(X30)|(X31=k1_xboole_0|(X31=k1_tarski(X30)|k1_tarski(X30)!=k2_xboole_0(X31,X32))))&(X32=k1_xboole_0|(X31=k1_xboole_0|(X31=k1_tarski(X30)|k1_tarski(X30)!=k2_xboole_0(X31,X32)))))&((X31=k1_tarski(X30)|(X32=k1_tarski(X30)|(X31=k1_tarski(X30)|k1_tarski(X30)!=k2_xboole_0(X31,X32))))&(X32=k1_xboole_0|(X32=k1_tarski(X30)|(X31=k1_tarski(X30)|k1_tarski(X30)!=k2_xboole_0(X31,X32))))))&(((X31=k1_tarski(X30)|(X31=k1_xboole_0|(X32=k1_tarski(X30)|k1_tarski(X30)!=k2_xboole_0(X31,X32))))&(X32=k1_xboole_0|(X31=k1_xboole_0|(X32=k1_tarski(X30)|k1_tarski(X30)!=k2_xboole_0(X31,X32)))))&((X31=k1_tarski(X30)|(X32=k1_tarski(X30)|(X32=k1_tarski(X30)|k1_tarski(X30)!=k2_xboole_0(X31,X32))))&(X32=k1_xboole_0|(X32=k1_tarski(X30)|(X32=k1_tarski(X30)|k1_tarski(X30)!=k2_xboole_0(X31,X32))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_zfmisc_1])])])).
% 0.12/0.40  fof(c_0_38, plain, ![X24, X25]:(v1_xboole_0(X25)|(~r1_tarski(X25,X24)|~r1_xboole_0(X25,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.12/0.40  fof(c_0_39, plain, ![X28, X29]:((~r1_xboole_0(X28,X29)|k4_xboole_0(X28,X29)=X28)&(k4_xboole_0(X28,X29)!=X28|r1_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.12/0.40  cnf(c_0_40, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.40  cnf(c_0_41, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.40  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,esk1_2(k4_xboole_0(X1,X2),X3)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.40  cnf(c_0_43, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(X1,X2))|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.40  cnf(c_0_44, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(X1,X2))|~r1_tarski(esk4_0,X2)), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.12/0.40  cnf(c_0_45, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.40  cnf(c_0_46, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|X1=k1_tarski(X2)|k1_tarski(X2)!=k2_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.40  fof(c_0_47, plain, ![X35, X36]:(v1_xboole_0(X35)|~m1_subset_1(X36,X35)|k6_domain_1(X35,X36)=k1_tarski(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.12/0.40  fof(c_0_48, plain, ![X37, X39]:(((m1_subset_1(esk2_1(X37),X37)|~v1_zfmisc_1(X37)|v1_xboole_0(X37))&(X37=k6_domain_1(X37,esk2_1(X37))|~v1_zfmisc_1(X37)|v1_xboole_0(X37)))&(~m1_subset_1(X39,X37)|X37!=k6_domain_1(X37,X39)|v1_zfmisc_1(X37)|v1_xboole_0(X37))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.12/0.40  cnf(c_0_49, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.40  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.40  cnf(c_0_51, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.40  cnf(c_0_52, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),X2)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.40  cnf(c_0_53, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(esk4_0,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.12/0.40  cnf(c_0_54, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|k1_tarski(X2)!=k2_xboole_0(X1,X3)), inference(cn,[status(thm)],[c_0_46])).
% 0.12/0.40  cnf(c_0_55, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.40  cnf(c_0_56, plain, (m1_subset_1(esk2_1(X1),X1)|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.40  cnf(c_0_57, plain, (v1_xboole_0(X1)|k4_xboole_0(X1,X2)!=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.40  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk3_0,X1)=k1_xboole_0|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.40  cnf(c_0_59, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_60, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_53, c_0_41])).
% 0.12/0.40  cnf(c_0_61, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|~r1_tarski(X1,k1_tarski(X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_45])])).
% 0.12/0.40  cnf(c_0_62, plain, (X1=k6_domain_1(X1,esk2_1(X1))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.40  cnf(c_0_63, plain, (k6_domain_1(X1,esk2_1(X1))=k1_tarski(esk2_1(X1))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.12/0.40  cnf(c_0_64, negated_conjecture, (esk3_0!=k1_xboole_0|~r1_tarski(esk4_0,X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60])).
% 0.12/0.40  cnf(c_0_65, negated_conjecture, (esk3_0=k1_tarski(X1)|esk3_0=k1_xboole_0|~r1_tarski(esk4_0,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 0.12/0.40  cnf(c_0_66, plain, (k1_tarski(esk2_1(X1))=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.12/0.40  cnf(c_0_67, negated_conjecture, (esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_20])).
% 0.12/0.40  cnf(c_0_68, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.40  cnf(c_0_69, negated_conjecture, (esk3_0=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)|~r1_tarski(esk4_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.12/0.40  cnf(c_0_70, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_68])).
% 0.12/0.40  cnf(c_0_71, negated_conjecture, (v1_zfmisc_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_72, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_73, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])]), c_0_72]), c_0_73]), ['proof']).
% 0.12/0.40  # SZS output end CNFRefutation
% 0.12/0.40  # Proof object total steps             : 75
% 0.12/0.40  # Proof object clause steps            : 44
% 0.12/0.40  # Proof object formula steps           : 31
% 0.12/0.40  # Proof object conjectures             : 19
% 0.12/0.40  # Proof object clause conjectures      : 16
% 0.12/0.40  # Proof object formula conjectures     : 3
% 0.12/0.40  # Proof object initial clauses used    : 21
% 0.12/0.40  # Proof object initial formulas used   : 15
% 0.12/0.40  # Proof object generating inferences   : 21
% 0.12/0.40  # Proof object simplifying inferences  : 10
% 0.12/0.40  # Training examples: 0 positive, 0 negative
% 0.12/0.40  # Parsed axioms                        : 15
% 0.12/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.40  # Initial clauses                      : 33
% 0.12/0.40  # Removed in clause preprocessing      : 0
% 0.12/0.40  # Initial clauses in saturation        : 33
% 0.12/0.40  # Processed clauses                    : 606
% 0.12/0.40  # ...of these trivial                  : 2
% 0.12/0.40  # ...subsumed                          : 366
% 0.12/0.40  # ...remaining for further processing  : 238
% 0.12/0.40  # Other redundant clauses eliminated   : 12
% 0.12/0.40  # Clauses deleted for lack of memory   : 0
% 0.12/0.40  # Backward-subsumed                    : 4
% 0.12/0.40  # Backward-rewritten                   : 6
% 0.12/0.40  # Generated clauses                    : 1658
% 0.12/0.40  # ...of the previous two non-trivial   : 1380
% 0.12/0.40  # Contextual simplify-reflections      : 5
% 0.12/0.40  # Paramodulations                      : 1646
% 0.12/0.40  # Factorizations                       : 0
% 0.12/0.40  # Equation resolutions                 : 12
% 0.12/0.40  # Propositional unsat checks           : 0
% 0.12/0.40  #    Propositional check models        : 0
% 0.12/0.40  #    Propositional check unsatisfiable : 0
% 0.12/0.40  #    Propositional clauses             : 0
% 0.12/0.40  #    Propositional clauses after purity: 0
% 0.12/0.40  #    Propositional unsat core size     : 0
% 0.12/0.40  #    Propositional preprocessing time  : 0.000
% 0.12/0.40  #    Propositional encoding time       : 0.000
% 0.12/0.40  #    Propositional solver time         : 0.000
% 0.12/0.40  #    Success case prop preproc time    : 0.000
% 0.12/0.40  #    Success case prop encoding time   : 0.000
% 0.12/0.40  #    Success case prop solver time     : 0.000
% 0.12/0.40  # Current number of processed clauses  : 199
% 0.12/0.40  #    Positive orientable unit clauses  : 13
% 0.12/0.40  #    Positive unorientable unit clauses: 0
% 0.12/0.40  #    Negative unit clauses             : 10
% 0.12/0.40  #    Non-unit-clauses                  : 176
% 0.12/0.40  # Current number of unprocessed clauses: 799
% 0.12/0.40  # ...number of literals in the above   : 2430
% 0.12/0.40  # Current number of archived formulas  : 0
% 0.12/0.40  # Current number of archived clauses   : 37
% 0.12/0.40  # Clause-clause subsumption calls (NU) : 7900
% 0.12/0.40  # Rec. Clause-clause subsumption calls : 5528
% 0.12/0.40  # Non-unit clause-clause subsumptions  : 223
% 0.12/0.40  # Unit Clause-clause subsumption calls : 195
% 0.12/0.40  # Rewrite failures with RHS unbound    : 0
% 0.12/0.40  # BW rewrite match attempts            : 14
% 0.12/0.40  # BW rewrite match successes           : 6
% 0.12/0.40  # Condensation attempts                : 0
% 0.12/0.40  # Condensation successes               : 0
% 0.12/0.40  # Termbank termtop insertions          : 19095
% 0.12/0.40  
% 0.12/0.40  # -------------------------------------------------
% 0.12/0.40  # User time                : 0.054 s
% 0.12/0.40  # System time              : 0.010 s
% 0.12/0.40  # Total time               : 0.065 s
% 0.12/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
