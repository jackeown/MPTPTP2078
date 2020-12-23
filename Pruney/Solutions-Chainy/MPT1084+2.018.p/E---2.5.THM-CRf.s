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
% DateTime   : Thu Dec  3 11:08:25 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 311 expanded)
%              Number of clauses        :   33 ( 112 expanded)
%              Number of leaves         :   11 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  220 (1438 expanded)
%              Number of equality atoms :   45 ( 203 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   25 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t201_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_funct_2(X2,X1,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => k3_funct_2(X1,X1,X2,X3) = X3 )
           => r2_funct_2(X1,X1,X2,k6_partfun1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(d9_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r2_funct_2(X1,X2,X3,X4)
          <=> ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_funct_2(X2,X1,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( ! [X3] :
                  ( m1_subset_1(X3,X1)
                 => k3_funct_2(X1,X1,X2,X3) = X3 )
             => r2_funct_2(X1,X1,X2,k6_partfun1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t201_funct_2])).

fof(c_0_12,plain,(
    ! [X12,X13,X14] :
      ( ( k1_relat_1(X13) = X12
        | X13 != k6_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(X14,X12)
        | k1_funct_1(X13,X14) = X14
        | X13 != k6_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | k1_relat_1(X13) != X12
        | X13 = k6_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( k1_funct_1(X13,esk1_2(X12,X13)) != esk1_2(X12,X13)
        | k1_relat_1(X13) != X12
        | X13 = k6_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

fof(c_0_13,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | v1_relat_1(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_14,negated_conjecture,(
    ! [X37] :
      ( ~ v1_xboole_0(esk3_0)
      & v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk3_0,esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
      & ( ~ m1_subset_1(X37,esk3_0)
        | k3_funct_2(esk3_0,esk3_0,esk4_0,X37) = X37 )
      & ~ r2_funct_2(esk3_0,esk3_0,esk4_0,k6_partfun1(esk3_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

fof(c_0_15,plain,(
    ! [X10,X11] : v1_relat_1(k2_zfmisc_1(X10,X11)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X19,X20,X21] :
      ( ( v1_funct_1(X21)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | v1_xboole_0(X20) )
      & ( v1_partfun1(X21,X19)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | v1_xboole_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_21,plain,(
    ! [X16,X17,X18] :
      ( ( v4_relat_1(X18,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( v5_relat_1(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_22,plain,(
    ! [X30,X31,X32,X33] :
      ( v1_xboole_0(X30)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,X30,X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | ~ m1_subset_1(X33,X30)
      | k3_funct_2(X30,X31,X32,X33) = k1_funct_1(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_23,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | m1_subset_1(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_24,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk1_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

fof(c_0_27,plain,(
    ! [X22,X23] :
      ( ( ~ v1_partfun1(X23,X22)
        | k1_relat_1(X23) = X22
        | ~ v1_relat_1(X23)
        | ~ v4_relat_1(X23,X22) )
      & ( k1_relat_1(X23) != X22
        | v1_partfun1(X23,X22)
        | ~ v1_relat_1(X23)
        | ~ v4_relat_1(X23,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_28,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk4_0)) = esk4_0
    | r2_hidden(esk1_2(k1_relat_1(esk4_0),esk4_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_35,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( v1_partfun1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_18]),c_0_29]),c_0_25])]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v4_relat_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_18])).

fof(c_0_38,plain,(
    ! [X34] : k6_partfun1(X34) = k6_relat_1(X34) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_39,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk1_2(X2,X1)) != esk1_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( k3_funct_2(esk3_0,esk3_0,esk4_0,X1) = X1
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( k3_funct_2(esk3_0,esk3_0,esk4_0,X1) = k1_funct_1(esk4_0,X1)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_29]),c_0_25])]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk4_0)) = esk4_0
    | m1_subset_1(esk1_2(k1_relat_1(esk4_0),esk4_0),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_26])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_funct_2(esk3_0,esk3_0,esk4_0,k6_partfun1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k1_funct_1(X1,esk1_2(k1_relat_1(X1),X1)) != esk1_2(k1_relat_1(X1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = X1
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0
    | m1_subset_1(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_43]),c_0_43])).

fof(c_0_49,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( ~ r2_funct_2(X24,X25,X26,X27)
        | ~ m1_subset_1(X28,X24)
        | k1_funct_1(X26,X28) = k1_funct_1(X27,X28)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X24,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( m1_subset_1(esk2_4(X24,X25,X26,X27),X24)
        | r2_funct_2(X24,X25,X26,X27)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X24,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( k1_funct_1(X26,esk2_4(X24,X25,X26,X27)) != k1_funct_1(X27,esk2_4(X24,X25,X26,X27))
        | r2_funct_2(X24,X25,X26,X27)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X24,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_funct_2(esk3_0,esk3_0,esk4_0,k6_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_43]),c_0_25]),c_0_26]),c_0_43])]),c_0_48])).

cnf(c_0_52,plain,
    ( r2_funct_2(X2,X3,X1,X4)
    | k1_funct_1(X1,esk2_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk2_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_funct_2(esk3_0,esk3_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29]),c_0_25]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.30  % Computer   : n012.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 12:12:37 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.30  # Version: 2.5pre002
% 0.11/0.30  # No SInE strategy applied
% 0.11/0.30  # Trying AutoSched0 for 299 seconds
% 0.16/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.16/0.34  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.16/0.34  #
% 0.16/0.34  # Preprocessing time       : 0.029 s
% 0.16/0.34  # Presaturation interreduction done
% 0.16/0.34  
% 0.16/0.34  # Proof found!
% 0.16/0.34  # SZS status Theorem
% 0.16/0.34  # SZS output start CNFRefutation
% 0.16/0.34  fof(t201_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(![X3]:(m1_subset_1(X3,X1)=>k3_funct_2(X1,X1,X2,X3)=X3)=>r2_funct_2(X1,X1,X2,k6_partfun1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 0.16/0.34  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 0.16/0.34  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.16/0.34  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.16/0.34  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.16/0.34  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.16/0.34  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.16/0.34  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.16/0.34  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.16/0.34  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.16/0.34  fof(d9_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_2)).
% 0.16/0.34  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(![X3]:(m1_subset_1(X3,X1)=>k3_funct_2(X1,X1,X2,X3)=X3)=>r2_funct_2(X1,X1,X2,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t201_funct_2])).
% 0.16/0.34  fof(c_0_12, plain, ![X12, X13, X14]:(((k1_relat_1(X13)=X12|X13!=k6_relat_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(~r2_hidden(X14,X12)|k1_funct_1(X13,X14)=X14|X13!=k6_relat_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))))&((r2_hidden(esk1_2(X12,X13),X12)|k1_relat_1(X13)!=X12|X13=k6_relat_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(k1_funct_1(X13,esk1_2(X12,X13))!=esk1_2(X12,X13)|k1_relat_1(X13)!=X12|X13=k6_relat_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.16/0.34  fof(c_0_13, plain, ![X8, X9]:(~v1_relat_1(X8)|(~m1_subset_1(X9,k1_zfmisc_1(X8))|v1_relat_1(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.16/0.34  fof(c_0_14, negated_conjecture, ![X37]:(~v1_xboole_0(esk3_0)&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk3_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))))&((~m1_subset_1(X37,esk3_0)|k3_funct_2(esk3_0,esk3_0,esk4_0,X37)=X37)&~r2_funct_2(esk3_0,esk3_0,esk4_0,k6_partfun1(esk3_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.16/0.34  fof(c_0_15, plain, ![X10, X11]:v1_relat_1(k2_zfmisc_1(X10,X11)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.16/0.34  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|X2=k6_relat_1(X1)|k1_relat_1(X2)!=X1|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.16/0.34  cnf(c_0_17, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.16/0.34  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.34  cnf(c_0_19, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.16/0.34  fof(c_0_20, plain, ![X19, X20, X21]:((v1_funct_1(X21)|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|v1_xboole_0(X20))&(v1_partfun1(X21,X19)|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|v1_xboole_0(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.16/0.34  fof(c_0_21, plain, ![X16, X17, X18]:((v4_relat_1(X18,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(v5_relat_1(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.16/0.34  fof(c_0_22, plain, ![X30, X31, X32, X33]:(v1_xboole_0(X30)|~v1_funct_1(X32)|~v1_funct_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~m1_subset_1(X33,X30)|k3_funct_2(X30,X31,X32,X33)=k1_funct_1(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.16/0.34  fof(c_0_23, plain, ![X6, X7]:(~r2_hidden(X6,X7)|m1_subset_1(X6,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.16/0.34  cnf(c_0_24, plain, (k6_relat_1(k1_relat_1(X1))=X1|r2_hidden(esk1_2(k1_relat_1(X1),X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_16])).
% 0.16/0.34  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.34  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.16/0.34  fof(c_0_27, plain, ![X22, X23]:((~v1_partfun1(X23,X22)|k1_relat_1(X23)=X22|(~v1_relat_1(X23)|~v4_relat_1(X23,X22)))&(k1_relat_1(X23)!=X22|v1_partfun1(X23,X22)|(~v1_relat_1(X23)|~v4_relat_1(X23,X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.16/0.34  cnf(c_0_28, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.16/0.34  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk4_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.34  cnf(c_0_30, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.34  cnf(c_0_31, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.34  cnf(c_0_32, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.16/0.34  cnf(c_0_33, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.16/0.34  cnf(c_0_34, negated_conjecture, (k6_relat_1(k1_relat_1(esk4_0))=esk4_0|r2_hidden(esk1_2(k1_relat_1(esk4_0),esk4_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.16/0.34  cnf(c_0_35, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.34  cnf(c_0_36, negated_conjecture, (v1_partfun1(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_18]), c_0_29]), c_0_25])]), c_0_30])).
% 0.16/0.34  cnf(c_0_37, negated_conjecture, (v4_relat_1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_18])).
% 0.16/0.34  fof(c_0_38, plain, ![X34]:k6_partfun1(X34)=k6_relat_1(X34), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.16/0.34  cnf(c_0_39, plain, (X1=k6_relat_1(X2)|k1_funct_1(X1,esk1_2(X2,X1))!=esk1_2(X2,X1)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.16/0.34  cnf(c_0_40, negated_conjecture, (k3_funct_2(esk3_0,esk3_0,esk4_0,X1)=X1|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.34  cnf(c_0_41, negated_conjecture, (k3_funct_2(esk3_0,esk3_0,esk4_0,X1)=k1_funct_1(esk4_0,X1)|~m1_subset_1(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_18]), c_0_29]), c_0_25])]), c_0_30])).
% 0.16/0.34  cnf(c_0_42, negated_conjecture, (k6_relat_1(k1_relat_1(esk4_0))=esk4_0|m1_subset_1(esk1_2(k1_relat_1(esk4_0),esk4_0),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.16/0.34  cnf(c_0_43, negated_conjecture, (k1_relat_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_26])])).
% 0.16/0.34  cnf(c_0_44, negated_conjecture, (~r2_funct_2(esk3_0,esk3_0,esk4_0,k6_partfun1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.34  cnf(c_0_45, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.16/0.34  cnf(c_0_46, plain, (k6_relat_1(k1_relat_1(X1))=X1|k1_funct_1(X1,esk1_2(k1_relat_1(X1),X1))!=esk1_2(k1_relat_1(X1),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_39])).
% 0.16/0.34  cnf(c_0_47, negated_conjecture, (k1_funct_1(esk4_0,X1)=X1|~m1_subset_1(X1,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.16/0.34  cnf(c_0_48, negated_conjecture, (k6_relat_1(esk3_0)=esk4_0|m1_subset_1(esk1_2(esk3_0,esk4_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_43]), c_0_43])).
% 0.16/0.34  fof(c_0_49, plain, ![X24, X25, X26, X27, X28]:((~r2_funct_2(X24,X25,X26,X27)|(~m1_subset_1(X28,X24)|k1_funct_1(X26,X28)=k1_funct_1(X27,X28))|(~v1_funct_1(X27)|~v1_funct_2(X27,X24,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))|(~v1_funct_1(X26)|~v1_funct_2(X26,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))&((m1_subset_1(esk2_4(X24,X25,X26,X27),X24)|r2_funct_2(X24,X25,X26,X27)|(~v1_funct_1(X27)|~v1_funct_2(X27,X24,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))|(~v1_funct_1(X26)|~v1_funct_2(X26,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))&(k1_funct_1(X26,esk2_4(X24,X25,X26,X27))!=k1_funct_1(X27,esk2_4(X24,X25,X26,X27))|r2_funct_2(X24,X25,X26,X27)|(~v1_funct_1(X27)|~v1_funct_2(X27,X24,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))|(~v1_funct_1(X26)|~v1_funct_2(X26,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).
% 0.16/0.34  cnf(c_0_50, negated_conjecture, (~r2_funct_2(esk3_0,esk3_0,esk4_0,k6_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.16/0.34  cnf(c_0_51, negated_conjecture, (k6_relat_1(esk3_0)=esk4_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_43]), c_0_25]), c_0_26]), c_0_43])]), c_0_48])).
% 0.16/0.34  cnf(c_0_52, plain, (r2_funct_2(X2,X3,X1,X4)|k1_funct_1(X1,esk2_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk2_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.16/0.34  cnf(c_0_53, negated_conjecture, (~r2_funct_2(esk3_0,esk3_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.16/0.34  cnf(c_0_54, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_52])).
% 0.16/0.34  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_29]), c_0_25]), c_0_18])]), ['proof']).
% 0.16/0.34  # SZS output end CNFRefutation
% 0.16/0.34  # Proof object total steps             : 56
% 0.16/0.34  # Proof object clause steps            : 33
% 0.16/0.34  # Proof object formula steps           : 23
% 0.16/0.34  # Proof object conjectures             : 22
% 0.16/0.34  # Proof object clause conjectures      : 19
% 0.16/0.34  # Proof object formula conjectures     : 3
% 0.16/0.34  # Proof object initial clauses used    : 17
% 0.16/0.34  # Proof object initial formulas used   : 11
% 0.16/0.34  # Proof object generating inferences   : 11
% 0.16/0.34  # Proof object simplifying inferences  : 32
% 0.16/0.34  # Training examples: 0 positive, 0 negative
% 0.16/0.34  # Parsed axioms                        : 11
% 0.16/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.34  # Initial clauses                      : 24
% 0.16/0.34  # Removed in clause preprocessing      : 2
% 0.16/0.34  # Initial clauses in saturation        : 22
% 0.16/0.34  # Processed clauses                    : 72
% 0.16/0.34  # ...of these trivial                  : 0
% 0.16/0.34  # ...subsumed                          : 2
% 0.16/0.34  # ...remaining for further processing  : 70
% 0.16/0.34  # Other redundant clauses eliminated   : 5
% 0.16/0.34  # Clauses deleted for lack of memory   : 0
% 0.16/0.34  # Backward-subsumed                    : 0
% 0.16/0.34  # Backward-rewritten                   : 6
% 0.16/0.34  # Generated clauses                    : 35
% 0.16/0.34  # ...of the previous two non-trivial   : 33
% 0.16/0.34  # Contextual simplify-reflections      : 1
% 0.16/0.34  # Paramodulations                      : 29
% 0.16/0.34  # Factorizations                       : 0
% 0.16/0.34  # Equation resolutions                 : 6
% 0.16/0.34  # Propositional unsat checks           : 0
% 0.16/0.34  #    Propositional check models        : 0
% 0.16/0.34  #    Propositional check unsatisfiable : 0
% 0.16/0.34  #    Propositional clauses             : 0
% 0.16/0.34  #    Propositional clauses after purity: 0
% 0.16/0.34  #    Propositional unsat core size     : 0
% 0.16/0.34  #    Propositional preprocessing time  : 0.000
% 0.16/0.34  #    Propositional encoding time       : 0.000
% 0.16/0.34  #    Propositional solver time         : 0.000
% 0.16/0.34  #    Success case prop preproc time    : 0.000
% 0.16/0.34  #    Success case prop encoding time   : 0.000
% 0.16/0.34  #    Success case prop solver time     : 0.000
% 0.16/0.34  # Current number of processed clauses  : 37
% 0.16/0.34  #    Positive orientable unit clauses  : 11
% 0.16/0.34  #    Positive unorientable unit clauses: 0
% 0.16/0.34  #    Negative unit clauses             : 2
% 0.16/0.34  #    Non-unit-clauses                  : 24
% 0.16/0.34  # Current number of unprocessed clauses: 4
% 0.16/0.34  # ...number of literals in the above   : 36
% 0.16/0.34  # Current number of archived formulas  : 0
% 0.16/0.34  # Current number of archived clauses   : 29
% 0.16/0.34  # Clause-clause subsumption calls (NU) : 294
% 0.16/0.34  # Rec. Clause-clause subsumption calls : 19
% 0.16/0.34  # Non-unit clause-clause subsumptions  : 3
% 0.16/0.34  # Unit Clause-clause subsumption calls : 4
% 0.16/0.34  # Rewrite failures with RHS unbound    : 0
% 0.16/0.34  # BW rewrite match attempts            : 3
% 0.16/0.34  # BW rewrite match successes           : 2
% 0.16/0.34  # Condensation attempts                : 0
% 0.16/0.34  # Condensation successes               : 0
% 0.16/0.34  # Termbank termtop insertions          : 3181
% 0.16/0.34  
% 0.16/0.34  # -------------------------------------------------
% 0.16/0.34  # User time                : 0.031 s
% 0.16/0.34  # System time              : 0.004 s
% 0.16/0.34  # Total time               : 0.035 s
% 0.16/0.34  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
