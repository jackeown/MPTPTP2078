%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:19 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 586 expanded)
%              Number of clauses        :   64 ( 221 expanded)
%              Number of leaves         :   22 ( 146 expanded)
%              Depth                    :   13
%              Number of atoms          :  320 (2998 expanded)
%              Number of equality atoms :   44 ( 146 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
           => ( v2_funct_1(X3)
              & v2_funct_2(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t24_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))
           => k2_relset_1(X1,X2,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(fc4_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(t26_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))
           => ( ( X3 = k1_xboole_0
                & X2 != k1_xboole_0 )
              | v2_funct_1(X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(l222_relat_1,axiom,(
    ! [X1,X2] :
      ( v4_relat_1(k1_xboole_0,X1)
      & v5_relat_1(k1_xboole_0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
             => ( v2_funct_1(X3)
                & v2_funct_2(X4,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_funct_2])).

fof(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk3_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    & r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0))
    & ( ~ v2_funct_1(esk5_0)
      | ~ v2_funct_2(esk6_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_24,plain,(
    ! [X53] : k6_partfun1(X53) = k6_relat_1(X53) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_25,plain,(
    ! [X54,X55,X56,X57] :
      ( ~ v1_funct_1(X56)
      | ~ v1_funct_2(X56,X54,X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | ~ v1_funct_1(X57)
      | ~ v1_funct_2(X57,X55,X54)
      | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X54)))
      | ~ r2_relset_1(X55,X55,k1_partfun1(X55,X54,X54,X55,X57,X56),k6_partfun1(X55))
      | k2_relset_1(X54,X55,X56) = X55 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).

fof(c_0_26,plain,(
    ! [X40,X41,X42,X43] :
      ( ( ~ r2_relset_1(X40,X41,X42,X43)
        | X42 = X43
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X42 != X43
        | r2_relset_1(X40,X41,X42,X43)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_27,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X44] : m1_subset_1(k6_relat_1(X44),k1_zfmisc_1(k2_zfmisc_1(X44,X44))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_30,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_32,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_33,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | ~ v1_xboole_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_34,plain,(
    ! [X28] :
      ( v1_relat_1(k6_relat_1(X28))
      & v2_funct_1(k6_relat_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_35,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X45,X46] :
      ( ( ~ v2_funct_2(X46,X45)
        | k2_relat_1(X46) = X45
        | ~ v1_relat_1(X46)
        | ~ v5_relat_1(X46,X45) )
      & ( k2_relat_1(X46) != X45
        | v2_funct_2(X46,X45)
        | ~ v1_relat_1(X46)
        | ~ v5_relat_1(X46,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

fof(c_0_39,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k2_relset_1(X37,X38,X39) = k2_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_40,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_47,plain,(
    ! [X34,X35,X36] :
      ( ( v4_relat_1(X36,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( v5_relat_1(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_48,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | v1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_52,plain,(
    ! [X19,X20] :
      ( ~ v1_xboole_0(X19)
      | v1_xboole_0(k2_zfmisc_1(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).

fof(c_0_53,plain,(
    ! [X58,X59,X60,X61,X62] :
      ( ( X60 = k1_xboole_0
        | v2_funct_1(X61)
        | ~ v2_funct_1(k1_partfun1(X58,X59,X59,X60,X61,X62))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X59,X60)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X58,X59)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) )
      & ( X59 != k1_xboole_0
        | v2_funct_1(X61)
        | ~ v2_funct_1(k1_partfun1(X58,X59,X59,X60,X61,X62))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X59,X60)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X58,X59)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).

cnf(c_0_54,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( k6_relat_1(esk3_0) = k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0)
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_56,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_57,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( k2_relset_1(esk4_0,esk3_0,esk6_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_59,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_61,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_64,plain,(
    ! [X24,X25] :
      ( ( ~ v5_relat_1(X25,X24)
        | r1_tarski(k2_relat_1(X25),X24)
        | ~ v1_relat_1(X25) )
      & ( ~ r1_tarski(k2_relat_1(X25),X24)
        | v5_relat_1(X25,X24)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_65,plain,(
    ! [X26,X27] :
      ( v4_relat_1(k1_xboole_0,X26)
      & v5_relat_1(k1_xboole_0,X27) ) ),
    inference(variable_rename,[status(thm)],[l222_relat_1])).

cnf(c_0_66,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_67,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_45])).

cnf(c_0_69,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_71,negated_conjecture,
    ( v2_funct_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_72,plain,(
    ! [X47,X48,X49,X50,X51,X52] :
      ( ( v1_funct_1(k1_partfun1(X47,X48,X49,X50,X51,X52))
        | ~ v1_funct_1(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ v1_funct_1(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( m1_subset_1(k1_partfun1(X47,X48,X49,X50,X51,X52),k1_zfmisc_1(k2_zfmisc_1(X47,X50)))
        | ~ v1_funct_1(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ v1_funct_1(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_73,plain,
    ( v2_funct_2(X1,k2_relat_1(X1))
    | ~ v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_74,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_46])])).

cnf(c_0_75,negated_conjecture,
    ( v5_relat_1(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_46])).

cnf(c_0_76,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_46])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_79,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_80,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_81,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_82,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_84,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | v2_funct_1(esk5_0)
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_42]),c_0_41]),c_0_44]),c_0_43]),c_0_46]),c_0_45])])).

cnf(c_0_85,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_86,negated_conjecture,
    ( ~ v2_funct_1(esk5_0)
    | ~ v2_funct_2(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_87,negated_conjecture,
    ( v2_funct_2(esk6_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76])])).

fof(c_0_88,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | ~ r1_tarski(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_89,plain,
    ( X1 = X2
    | r2_hidden(esk1_1(X2),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_90,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82])])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_63])).

cnf(c_0_92,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_44]),c_0_43]),c_0_46]),c_0_45])])).

cnf(c_0_93,negated_conjecture,
    ( ~ v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_94,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_95,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | r2_hidden(esk1_1(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_50])).

cnf(c_0_97,negated_conjecture,
    ( k1_xboole_0 = esk3_0 ),
    inference(sr,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_98,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,esk1_1(X1)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_tarski(esk3_0,esk1_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_96])).

cnf(c_0_100,plain,
    ( r1_tarski(esk3_0,X1) ),
    inference(rw,[status(thm)],[c_0_90,c_0_97])).

cnf(c_0_101,plain,
    ( esk3_0 = X1
    | ~ r1_tarski(X1,esk1_1(X1)) ),
    inference(rw,[status(thm)],[c_0_98,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_103,plain,
    ( v2_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_67])).

cnf(c_0_104,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_105,plain,
    ( v2_funct_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_103,c_0_97])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_104]),c_0_105])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:28:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t29_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 0.19/0.38  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.19/0.38  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 0.19/0.38  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.19/0.38  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 0.19/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.38  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.19/0.38  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 0.19/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.38  fof(fc4_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 0.19/0.38  fof(t26_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))=>((X3=k1_xboole_0&X2!=k1_xboole_0)|v2_funct_1(X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.38  fof(l222_relat_1, axiom, ![X1, X2]:(v4_relat_1(k1_xboole_0,X1)&v5_relat_1(k1_xboole_0,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l222_relat_1)).
% 0.19/0.38  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.19/0.38  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.19/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.19/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.38  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1)))))), inference(assume_negation,[status(cth)],[t29_funct_2])).
% 0.19/0.38  fof(c_0_23, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk3_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))&(r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0))&(~v2_funct_1(esk5_0)|~v2_funct_2(esk6_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.19/0.38  fof(c_0_24, plain, ![X53]:k6_partfun1(X53)=k6_relat_1(X53), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.19/0.38  fof(c_0_25, plain, ![X54, X55, X56, X57]:(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X55)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X54)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X54)))|(~r2_relset_1(X55,X55,k1_partfun1(X55,X54,X54,X55,X57,X56),k6_partfun1(X55))|k2_relset_1(X54,X55,X56)=X55))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 0.19/0.38  fof(c_0_26, plain, ![X40, X41, X42, X43]:((~r2_relset_1(X40,X41,X42,X43)|X42=X43|(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))&(X42!=X43|r2_relset_1(X40,X41,X42,X43)|(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_28, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  fof(c_0_29, plain, ![X44]:m1_subset_1(k6_relat_1(X44),k1_zfmisc_1(k2_zfmisc_1(X44,X44))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.19/0.38  cnf(c_0_30, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  fof(c_0_31, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.38  fof(c_0_32, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  fof(c_0_33, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|~v1_xboole_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.38  fof(c_0_34, plain, ![X28]:(v1_relat_1(k6_relat_1(X28))&v2_funct_1(k6_relat_1(X28))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.19/0.38  cnf(c_0_35, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  cnf(c_0_37, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  fof(c_0_38, plain, ![X45, X46]:((~v2_funct_2(X46,X45)|k2_relat_1(X46)=X45|(~v1_relat_1(X46)|~v5_relat_1(X46,X45)))&(k2_relat_1(X46)!=X45|v2_funct_2(X46,X45)|(~v1_relat_1(X46)|~v5_relat_1(X46,X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.19/0.38  fof(c_0_39, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k2_relset_1(X37,X38,X39)=k2_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.38  cnf(c_0_40, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_30, c_0_28])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  fof(c_0_47, plain, ![X34, X35, X36]:((v4_relat_1(X36,X34)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(v5_relat_1(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.38  fof(c_0_48, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.38  cnf(c_0_49, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_50, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_51, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  fof(c_0_52, plain, ![X19, X20]:(~v1_xboole_0(X19)|v1_xboole_0(k2_zfmisc_1(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).
% 0.19/0.38  fof(c_0_53, plain, ![X58, X59, X60, X61, X62]:((X60=k1_xboole_0|v2_funct_1(X61)|~v2_funct_1(k1_partfun1(X58,X59,X59,X60,X61,X62))|(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))|(~v1_funct_1(X61)|~v1_funct_2(X61,X58,X59)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))))&(X59!=k1_xboole_0|v2_funct_1(X61)|~v2_funct_1(k1_partfun1(X58,X59,X59,X60,X61,X62))|(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))|(~v1_funct_1(X61)|~v1_funct_2(X61,X58,X59)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).
% 0.19/0.38  cnf(c_0_54, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (k6_relat_1(esk3_0)=k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0)|~m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.19/0.38  cnf(c_0_56, plain, (v2_funct_2(X1,X2)|k2_relat_1(X1)!=X2|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_57, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (k2_relset_1(esk4_0,esk3_0,esk6_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])])).
% 0.19/0.38  cnf(c_0_59, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.38  cnf(c_0_60, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.38  fof(c_0_61, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  cnf(c_0_62, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.38  cnf(c_0_63, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  fof(c_0_64, plain, ![X24, X25]:((~v5_relat_1(X25,X24)|r1_tarski(k2_relat_1(X25),X24)|~v1_relat_1(X25))&(~r1_tarski(k2_relat_1(X25),X24)|v5_relat_1(X25,X24)|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.38  fof(c_0_65, plain, ![X26, X27]:(v4_relat_1(k1_xboole_0,X26)&v5_relat_1(k1_xboole_0,X27)), inference(variable_rename,[status(thm)],[l222_relat_1])).
% 0.19/0.38  cnf(c_0_66, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_67, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_45])).
% 0.19/0.38  cnf(c_0_69, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.38  cnf(c_0_70, plain, (X1=k1_xboole_0|v2_funct_1(X2)|~v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (v2_funct_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0))|~m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.38  fof(c_0_72, plain, ![X47, X48, X49, X50, X51, X52]:((v1_funct_1(k1_partfun1(X47,X48,X49,X50,X51,X52))|(~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|~v1_funct_1(X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))&(m1_subset_1(k1_partfun1(X47,X48,X49,X50,X51,X52),k1_zfmisc_1(k2_zfmisc_1(X47,X50)))|(~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|~v1_funct_1(X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.19/0.38  cnf(c_0_73, plain, (v2_funct_2(X1,k2_relat_1(X1))|~v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_56])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (k2_relat_1(esk6_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_46])])).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (v5_relat_1(esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_59, c_0_46])).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_60, c_0_46])).
% 0.19/0.38  cnf(c_0_77, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.38  cnf(c_0_78, plain, (r1_tarski(X1,X2)|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.38  cnf(c_0_79, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.38  cnf(c_0_80, plain, (v5_relat_1(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.38  cnf(c_0_81, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.38  cnf(c_0_82, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.38  cnf(c_0_83, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.38  cnf(c_0_84, negated_conjecture, (k1_xboole_0=esk3_0|v2_funct_1(esk5_0)|~m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_42]), c_0_41]), c_0_44]), c_0_43]), c_0_46]), c_0_45])])).
% 0.19/0.38  cnf(c_0_85, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.38  cnf(c_0_86, negated_conjecture, (~v2_funct_1(esk5_0)|~v2_funct_2(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_87, negated_conjecture, (v2_funct_2(esk6_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_76])])).
% 0.19/0.38  fof(c_0_88, plain, ![X29, X30]:(~r2_hidden(X29,X30)|~r1_tarski(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.38  cnf(c_0_89, plain, (X1=X2|r2_hidden(esk1_1(X2),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.38  cnf(c_0_90, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_82])])).
% 0.19/0.38  cnf(c_0_91, negated_conjecture, (r2_hidden(esk1_1(esk3_0),esk3_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_83, c_0_63])).
% 0.19/0.38  cnf(c_0_92, negated_conjecture, (k1_xboole_0=esk3_0|v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_44]), c_0_43]), c_0_46]), c_0_45])])).
% 0.19/0.38  cnf(c_0_93, negated_conjecture, (~v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 0.19/0.38  cnf(c_0_94, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.19/0.38  cnf(c_0_95, plain, (k1_xboole_0=X1|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.19/0.38  cnf(c_0_96, negated_conjecture, (r1_tarski(esk5_0,X1)|r2_hidden(esk1_1(esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_91, c_0_50])).
% 0.19/0.38  cnf(c_0_97, negated_conjecture, (k1_xboole_0=esk3_0), inference(sr,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.38  cnf(c_0_98, plain, (k1_xboole_0=X1|~r1_tarski(X1,esk1_1(X1))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.38  cnf(c_0_99, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_tarski(esk3_0,esk1_1(esk3_0))), inference(spm,[status(thm)],[c_0_94, c_0_96])).
% 0.19/0.38  cnf(c_0_100, plain, (r1_tarski(esk3_0,X1)), inference(rw,[status(thm)],[c_0_90, c_0_97])).
% 0.19/0.38  cnf(c_0_101, plain, (esk3_0=X1|~r1_tarski(X1,esk1_1(X1))), inference(rw,[status(thm)],[c_0_98, c_0_97])).
% 0.19/0.38  cnf(c_0_102, negated_conjecture, (r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])])).
% 0.19/0.38  cnf(c_0_103, plain, (v2_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_67])).
% 0.19/0.38  cnf(c_0_104, negated_conjecture, (esk5_0=esk3_0), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.19/0.38  cnf(c_0_105, plain, (v2_funct_1(esk3_0)), inference(rw,[status(thm)],[c_0_103, c_0_97])).
% 0.19/0.38  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_104]), c_0_105])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 107
% 0.19/0.38  # Proof object clause steps            : 64
% 0.19/0.38  # Proof object formula steps           : 43
% 0.19/0.38  # Proof object conjectures             : 31
% 0.19/0.38  # Proof object clause conjectures      : 28
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 31
% 0.19/0.38  # Proof object initial formulas used   : 22
% 0.19/0.38  # Proof object generating inferences   : 23
% 0.19/0.38  # Proof object simplifying inferences  : 43
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 22
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 43
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 42
% 0.19/0.38  # Processed clauses                    : 220
% 0.19/0.38  # ...of these trivial                  : 1
% 0.19/0.38  # ...subsumed                          : 29
% 0.19/0.38  # ...remaining for further processing  : 190
% 0.19/0.38  # Other redundant clauses eliminated   : 5
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 6
% 0.19/0.38  # Backward-rewritten                   : 57
% 0.19/0.38  # Generated clauses                    : 262
% 0.19/0.38  # ...of the previous two non-trivial   : 251
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 256
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 5
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 80
% 0.19/0.38  #    Positive orientable unit clauses  : 28
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 0
% 0.19/0.38  #    Non-unit-clauses                  : 52
% 0.19/0.38  # Current number of unprocessed clauses: 114
% 0.19/0.38  # ...number of literals in the above   : 298
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 106
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1342
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 470
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 33
% 0.19/0.38  # Unit Clause-clause subsumption calls : 173
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 9
% 0.19/0.38  # BW rewrite match successes           : 7
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 6450
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.040 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.045 s
% 0.19/0.38  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
