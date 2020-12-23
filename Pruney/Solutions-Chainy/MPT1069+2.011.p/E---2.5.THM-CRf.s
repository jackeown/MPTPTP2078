%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:50 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 213 expanded)
%              Number of clauses        :   44 (  74 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  289 (1446 expanded)
%              Number of equality atoms :   51 ( 281 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t186_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => ( X2 = k1_xboole_0
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k7_partfun1(X1,X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc6_funct_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & ~ v1_xboole_0(X3)
              & v1_funct_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(d8_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => k7_partfun1(X1,X2,X3) = k1_funct_1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(t8_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(k2_relset_1(X1,X2,X4),X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(t185_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => ( X2 = k1_xboole_0
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k1_funct_1(X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
           => ! [X5] :
                ( ( v1_funct_1(X5)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
               => ! [X6] :
                    ( m1_subset_1(X6,X2)
                   => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                     => ( X2 = k1_xboole_0
                        | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k7_partfun1(X1,X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t186_funct_2])).

fof(c_0_15,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_16,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v1_funct_1(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))
    & m1_subset_1(esk6_0,esk2_0)
    & r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0))
    & esk2_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0) != k7_partfun1(esk1_0,esk5_0,k1_funct_1(esk4_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X23,X24,X25] :
      ( ( v1_funct_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | v1_xboole_0(X23)
        | v1_xboole_0(X24) )
      & ( ~ v1_xboole_0(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | v1_xboole_0(X23)
        | v1_xboole_0(X24) )
      & ( v1_funct_2(X25,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | v1_xboole_0(X23)
        | v1_xboole_0(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).

fof(c_0_18,plain,(
    ! [X10] :
      ( ~ v1_xboole_0(X10)
      | v1_funct_1(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

fof(c_0_19,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X27)
      | ~ v5_relat_1(X27,X26)
      | ~ v1_funct_1(X27)
      | ~ r2_hidden(X28,k1_relat_1(X27))
      | k7_partfun1(X26,X27,X28) = k1_funct_1(X27,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_20,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X39,X40,X41,X42] :
      ( ( v1_funct_1(X42)
        | X40 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X39,X40,X42),X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X39,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( v1_funct_2(X42,X39,X41)
        | X40 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X39,X40,X42),X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X39,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X41)))
        | X40 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X39,X40,X42),X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X39,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( v1_funct_1(X42)
        | X39 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X39,X40,X42),X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X39,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( v1_funct_2(X42,X39,X41)
        | X39 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X39,X40,X42),X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X39,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X41)))
        | X39 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X39,X40,X42),X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X39,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0) != k7_partfun1(esk1_0,esk5_0,k1_funct_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_29,plain,(
    ! [X29,X30,X31,X32,X33,X34] :
      ( v1_xboole_0(X31)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,X30,X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | ~ v1_funct_1(X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X29)))
      | ~ m1_subset_1(X34,X30)
      | ~ r1_tarski(k2_relset_1(X30,X31,X32),k1_relset_1(X31,X29,X33))
      | X30 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X30,X31,X29,X32,X33),X34) = k1_funct_1(X33,k1_funct_1(X32,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

fof(c_0_30,plain,(
    ! [X14,X15,X16] :
      ( ( v4_relat_1(X16,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( v5_relat_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_31,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,X35,X36)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | ~ r2_hidden(X37,X35)
      | X36 = k1_xboole_0
      | r2_hidden(k1_funct_1(X38,X37),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_32,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_38,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))
    | ~ v5_relat_1(esk5_0,esk1_0)
    | ~ r2_hidden(k1_funct_1(esk4_0,esk6_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_28])])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | X3 = k1_xboole_0
    | k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6) = k1_funct_1(X4,k1_funct_1(X2,X6))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
    | ~ m1_subset_1(X6,X3)
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk6_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_funct_2(esk4_0,esk2_0,k1_relset_1(esk3_0,esk1_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_48,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relset_1(esk3_0,esk1_0,esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_34]),c_0_35]),c_0_36])])).

fof(c_0_49,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k1_relset_1(X20,X21,X22) = k1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_50,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_xboole_0(X17)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X17)))
      | v1_xboole_0(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_36])]),c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( ~ v5_relat_1(esk5_0,esk1_0)
    | ~ r2_hidden(k1_funct_1(esk4_0,esk6_0),k1_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_33]),c_0_34]),c_0_27]),c_0_35]),c_0_21]),c_0_36]),c_0_43])]),c_0_44]),c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( v5_relat_1(esk5_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( k1_relset_1(esk3_0,esk1_0,esk5_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk4_0,X1),k1_relset_1(esk3_0,esk1_0,esk5_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_35])]),c_0_48])).

cnf(c_0_56,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_57,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_44])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk4_0,esk6_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_61,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk4_0,X1),k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_21])])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_xboole_0(k1_relset_1(esk3_0,esk1_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_48]),c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | ~ r2_hidden(esk6_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk6_0,esk2_0)
    | v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_43])).

cnf(c_0_66,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_xboole_0(k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_56]),c_0_21])])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_69,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_69]),c_0_44])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_70]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:53:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.029 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 0.13/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.37  fof(cc6_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&~(v1_xboole_0(X3)))&v1_funct_2(X3,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 0.13/0.37  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.13/0.37  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 0.13/0.37  fof(t8_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 0.13/0.37  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 0.13/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.37  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.13/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.37  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.37  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.13/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.37  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.13/0.37  fof(c_0_15, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|v1_relat_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.37  fof(c_0_16, negated_conjecture, (~v1_xboole_0(esk3_0)&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((v1_funct_1(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))))&(m1_subset_1(esk6_0,esk2_0)&(r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0))&(esk2_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0)!=k7_partfun1(esk1_0,esk5_0,k1_funct_1(esk4_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.13/0.37  fof(c_0_17, plain, ![X23, X24, X25]:(((v1_funct_1(X25)|(~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|(v1_xboole_0(X23)|v1_xboole_0(X24)))&(~v1_xboole_0(X25)|(~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|(v1_xboole_0(X23)|v1_xboole_0(X24))))&(v1_funct_2(X25,X23,X24)|(~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|(v1_xboole_0(X23)|v1_xboole_0(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).
% 0.13/0.37  fof(c_0_18, plain, ![X10]:(~v1_xboole_0(X10)|v1_funct_1(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.13/0.37  fof(c_0_19, plain, ![X26, X27, X28]:(~v1_relat_1(X27)|~v5_relat_1(X27,X26)|~v1_funct_1(X27)|(~r2_hidden(X28,k1_relat_1(X27))|k7_partfun1(X26,X27,X28)=k1_funct_1(X27,X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.13/0.37  cnf(c_0_20, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  fof(c_0_22, plain, ![X39, X40, X41, X42]:((((v1_funct_1(X42)|X40=k1_xboole_0|~r1_tarski(k2_relset_1(X39,X40,X42),X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,X39,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&(v1_funct_2(X42,X39,X41)|X40=k1_xboole_0|~r1_tarski(k2_relset_1(X39,X40,X42),X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,X39,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))))&(m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X41)))|X40=k1_xboole_0|~r1_tarski(k2_relset_1(X39,X40,X42),X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,X39,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))))&(((v1_funct_1(X42)|X39!=k1_xboole_0|~r1_tarski(k2_relset_1(X39,X40,X42),X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,X39,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&(v1_funct_2(X42,X39,X41)|X39!=k1_xboole_0|~r1_tarski(k2_relset_1(X39,X40,X42),X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,X39,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))))&(m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X41)))|X39!=k1_xboole_0|~r1_tarski(k2_relset_1(X39,X40,X42),X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,X39,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).
% 0.13/0.37  cnf(c_0_23, plain, (v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_24, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0)!=k7_partfun1(esk1_0,esk5_0,k1_funct_1(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_26, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  fof(c_0_29, plain, ![X29, X30, X31, X32, X33, X34]:(v1_xboole_0(X31)|(~v1_funct_1(X32)|~v1_funct_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X29)))|(~m1_subset_1(X34,X30)|(~r1_tarski(k2_relset_1(X30,X31,X32),k1_relset_1(X31,X29,X33))|(X30=k1_xboole_0|k1_funct_1(k8_funct_2(X30,X31,X29,X32,X33),X34)=k1_funct_1(X33,k1_funct_1(X32,X34)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.13/0.37  fof(c_0_30, plain, ![X14, X15, X16]:((v4_relat_1(X16,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))&(v5_relat_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.37  fof(c_0_31, plain, ![X35, X36, X37, X38]:(~v1_funct_1(X38)|~v1_funct_2(X38,X35,X36)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|(~r2_hidden(X37,X35)|(X36=k1_xboole_0|r2_hidden(k1_funct_1(X38,X37),X36)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.13/0.37  cnf(c_0_32, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  fof(c_0_38, plain, ![X7]:(~v1_xboole_0(X7)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.37  cnf(c_0_39, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0)!=k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))|~v5_relat_1(esk5_0,esk1_0)|~r2_hidden(k1_funct_1(esk4_0,esk6_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])]), c_0_28])])).
% 0.13/0.37  cnf(c_0_42, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk6_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_45, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.37  cnf(c_0_46, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (esk3_0=k1_xboole_0|v1_funct_2(esk4_0,esk2_0,k1_relset_1(esk3_0,esk1_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36])])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relset_1(esk3_0,esk1_0,esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_34]), c_0_35]), c_0_36])])).
% 0.13/0.37  fof(c_0_49, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k1_relset_1(X20,X21,X22)=k1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.37  fof(c_0_50, plain, ![X17, X18, X19]:(~v1_xboole_0(X17)|(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X17)))|v1_xboole_0(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.13/0.37  cnf(c_0_51, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (v1_xboole_0(esk2_0)|~v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_36])]), c_0_40])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (~v5_relat_1(esk5_0,esk1_0)|~r2_hidden(k1_funct_1(esk4_0,esk6_0),k1_relat_1(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_33]), c_0_34]), c_0_27]), c_0_35]), c_0_21]), c_0_36]), c_0_43])]), c_0_44]), c_0_40])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (v5_relat_1(esk5_0,esk1_0)), inference(spm,[status(thm)],[c_0_45, c_0_21])).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, (k1_relset_1(esk3_0,esk1_0,esk5_0)=k1_xboole_0|esk3_0=k1_xboole_0|r2_hidden(k1_funct_1(esk4_0,X1),k1_relset_1(esk3_0,esk1_0,esk5_0))|~r2_hidden(X1,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_35])]), c_0_48])).
% 0.13/0.37  cnf(c_0_56, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.37  fof(c_0_57, plain, ![X8, X9]:(~m1_subset_1(X8,X9)|(v1_xboole_0(X9)|r2_hidden(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.37  cnf(c_0_58, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.37  cnf(c_0_59, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_44])).
% 0.13/0.37  cnf(c_0_60, negated_conjecture, (~r2_hidden(k1_funct_1(esk4_0,esk6_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])])).
% 0.13/0.37  cnf(c_0_61, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|esk3_0=k1_xboole_0|r2_hidden(k1_funct_1(esk4_0,X1),k1_relat_1(esk5_0))|~r2_hidden(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_21])])).
% 0.13/0.37  cnf(c_0_62, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.37  cnf(c_0_63, negated_conjecture, (esk3_0=k1_xboole_0|~v1_xboole_0(k1_relset_1(esk3_0,esk1_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_48]), c_0_59])).
% 0.13/0.37  cnf(c_0_64, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|esk3_0=k1_xboole_0|~r2_hidden(esk6_0,esk2_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.37  cnf(c_0_65, negated_conjecture, (r2_hidden(esk6_0,esk2_0)|v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_43])).
% 0.13/0.37  cnf(c_0_66, negated_conjecture, (esk3_0=k1_xboole_0|~v1_xboole_0(k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_56]), c_0_21])])).
% 0.13/0.37  cnf(c_0_67, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|esk3_0=k1_xboole_0|v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.37  cnf(c_0_68, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.37  cnf(c_0_69, negated_conjecture, (esk3_0=k1_xboole_0|v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])])).
% 0.13/0.37  cnf(c_0_70, negated_conjecture, (esk3_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_69]), c_0_44])).
% 0.13/0.37  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_70]), c_0_68])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 72
% 0.13/0.37  # Proof object clause steps            : 44
% 0.13/0.37  # Proof object formula steps           : 28
% 0.13/0.37  # Proof object conjectures             : 32
% 0.13/0.37  # Proof object clause conjectures      : 29
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 24
% 0.13/0.37  # Proof object initial formulas used   : 14
% 0.13/0.37  # Proof object generating inferences   : 17
% 0.13/0.37  # Proof object simplifying inferences  : 43
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 14
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 31
% 0.13/0.37  # Removed in clause preprocessing      : 4
% 0.13/0.37  # Initial clauses in saturation        : 27
% 0.13/0.37  # Processed clauses                    : 111
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 12
% 0.13/0.37  # ...remaining for further processing  : 99
% 0.13/0.37  # Other redundant clauses eliminated   : 2
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 3
% 0.13/0.37  # Backward-rewritten                   : 35
% 0.13/0.37  # Generated clauses                    : 69
% 0.13/0.37  # ...of the previous two non-trivial   : 76
% 0.13/0.37  # Contextual simplify-reflections      : 2
% 0.13/0.37  # Paramodulations                      : 67
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 2
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 32
% 0.13/0.37  #    Positive orientable unit clauses  : 10
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 3
% 0.13/0.37  #    Non-unit-clauses                  : 19
% 0.13/0.37  # Current number of unprocessed clauses: 9
% 0.13/0.37  # ...number of literals in the above   : 29
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 65
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 957
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 247
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 13
% 0.13/0.37  # Unit Clause-clause subsumption calls : 19
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 2
% 0.13/0.37  # BW rewrite match successes           : 2
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 3862
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.035 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.040 s
% 0.13/0.37  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
