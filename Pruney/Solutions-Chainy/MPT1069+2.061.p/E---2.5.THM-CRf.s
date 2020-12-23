%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 209 expanded)
%              Number of clauses        :   51 (  81 expanded)
%              Number of leaves         :   16 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  296 (1171 expanded)
%              Number of equality atoms :   81 ( 263 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(d8_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => k7_partfun1(X1,X2,X3) = k1_funct_1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X25,X26,X27,X29,X30,X31,X33] :
      ( ( r2_hidden(esk3_3(X25,X26,X27),k1_relat_1(X25))
        | ~ r2_hidden(X27,X26)
        | X26 != k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( X27 = k1_funct_1(X25,esk3_3(X25,X26,X27))
        | ~ r2_hidden(X27,X26)
        | X26 != k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(X30,k1_relat_1(X25))
        | X29 != k1_funct_1(X25,X30)
        | r2_hidden(X29,X26)
        | X26 != k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(esk4_2(X25,X31),X31)
        | ~ r2_hidden(X33,k1_relat_1(X25))
        | esk4_2(X25,X31) != k1_funct_1(X25,X33)
        | X31 = k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( r2_hidden(esk5_2(X25,X31),k1_relat_1(X25))
        | r2_hidden(esk4_2(X25,X31),X31)
        | X31 = k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( esk4_2(X25,X31) = k1_funct_1(X25,esk5_2(X25,X31))
        | r2_hidden(esk4_2(X25,X31),X31)
        | X31 = k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_18,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k1_relset_1(X40,X41,X42) = k1_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0)
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,esk7_0,esk8_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))
    & v1_funct_1(esk10_0)
    & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk6_0)))
    & m1_subset_1(esk11_0,esk7_0)
    & r1_tarski(k2_relset_1(esk7_0,esk8_0,esk9_0),k1_relset_1(esk8_0,esk6_0,esk10_0))
    & esk7_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0) != k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_20,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k2_relset_1(X43,X44,X45) = k2_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X46,X47,X48] :
      ( ( ~ v1_funct_2(X48,X46,X47)
        | X46 = k1_relset_1(X46,X47,X48)
        | X47 = k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( X46 != k1_relset_1(X46,X47,X48)
        | v1_funct_2(X48,X46,X47)
        | X47 = k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( ~ v1_funct_2(X48,X46,X47)
        | X46 = k1_relset_1(X46,X47,X48)
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( X46 != k1_relset_1(X46,X47,X48)
        | v1_funct_2(X48,X46,X47)
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( ~ v1_funct_2(X48,X46,X47)
        | X48 = k1_xboole_0
        | X46 = k1_xboole_0
        | X47 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( X48 != k1_xboole_0
        | v1_funct_2(X48,X46,X47)
        | X46 = k1_xboole_0
        | X47 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_23,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | v1_relat_1(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_26,plain,(
    ! [X23,X24] : v1_relat_1(k2_zfmisc_1(X23,X24)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_27,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,X20)
      | v1_xboole_0(X20)
      | r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | X1 != k1_funct_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( k1_relset_1(esk7_0,esk8_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X17] :
      ( ~ v1_xboole_0(X17)
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk11_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_39,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk7_0,esk8_0,esk9_0),k1_relset_1(esk8_0,esk6_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( k1_relset_1(esk8_0,esk6_0,esk10_0) = k1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( k2_relset_1(esk7_0,esk8_0,esk9_0) = k2_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_43,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk7_0
    | esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_32]),c_0_33])])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_24]),c_0_35])])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk11_0,esk7_0)
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_50,plain,(
    ! [X52,X53,X54,X55,X56,X57] :
      ( v1_xboole_0(X54)
      | ~ v1_funct_1(X55)
      | ~ v1_funct_2(X55,X53,X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
      | ~ v1_funct_1(X56)
      | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X52)))
      | ~ m1_subset_1(X57,X53)
      | ~ r1_tarski(k2_relset_1(X53,X54,X55),k1_relset_1(X54,X52,X56))
      | X53 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X53,X54,X52,X55,X56),X57) = k1_funct_1(X56,k1_funct_1(X55,X57)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

cnf(c_0_51,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk9_0),k1_relat_1(esk10_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk9_0,X1),k2_relat_1(esk9_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk11_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_55,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_58,plain,(
    ! [X49,X50,X51] :
      ( ~ v1_relat_1(X50)
      | ~ v5_relat_1(X50,X49)
      | ~ v1_funct_1(X50)
      | ~ r2_hidden(X51,k1_relat_1(X50))
      | k7_partfun1(X49,X50,X51) = k1_funct_1(X50,X51) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk10_0))
    | ~ r2_hidden(X1,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk9_0,esk11_0),k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_61,plain,(
    ! [X37,X38,X39] :
      ( ( v4_relat_1(X39,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( v5_relat_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk8_0,esk6_0,X2,esk10_0),X3) = k1_funct_1(esk10_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk8_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk8_0)))
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(k2_relset_1(X1,esk8_0,X2),k1_relat_1(esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_28]),c_0_56]),c_0_41])]),c_0_57])).

cnf(c_0_63,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk9_0,esk11_0),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_35])])).

cnf(c_0_66,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),X1) = k1_funct_1(esk10_0,k1_funct_1(esk9_0,X1))
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_33]),c_0_45]),c_0_24]),c_0_42]),c_0_52])]),c_0_49])).

fof(c_0_68,plain,(
    ! [X35,X36] :
      ( ~ r2_hidden(X35,X36)
      | ~ r1_tarski(X36,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_69,plain,(
    ! [X18] : r1_tarski(k1_xboole_0,X18) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_70,negated_conjecture,
    ( k7_partfun1(X1,esk10_0,k1_funct_1(esk9_0,esk11_0)) = k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0))
    | esk8_0 = k1_xboole_0
    | ~ v5_relat_1(esk10_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_56]),c_0_65])])).

cnf(c_0_71,negated_conjecture,
    ( v5_relat_1(esk10_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_28])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0) != k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_73,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0) = k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_38])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_76,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_77,negated_conjecture,
    ( k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0)) = k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0))
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0)) != k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_81]),c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:28:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.19/0.42  # and selection function SelectNewComplexAHP.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.028 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 0.19/0.42  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.42  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.42  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.42  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.42  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.42  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.42  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 0.19/0.42  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 0.19/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.42  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.42  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.42  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.19/0.42  fof(c_0_17, plain, ![X25, X26, X27, X29, X30, X31, X33]:((((r2_hidden(esk3_3(X25,X26,X27),k1_relat_1(X25))|~r2_hidden(X27,X26)|X26!=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(X27=k1_funct_1(X25,esk3_3(X25,X26,X27))|~r2_hidden(X27,X26)|X26!=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&(~r2_hidden(X30,k1_relat_1(X25))|X29!=k1_funct_1(X25,X30)|r2_hidden(X29,X26)|X26!=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&((~r2_hidden(esk4_2(X25,X31),X31)|(~r2_hidden(X33,k1_relat_1(X25))|esk4_2(X25,X31)!=k1_funct_1(X25,X33))|X31=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&((r2_hidden(esk5_2(X25,X31),k1_relat_1(X25))|r2_hidden(esk4_2(X25,X31),X31)|X31=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(esk4_2(X25,X31)=k1_funct_1(X25,esk5_2(X25,X31))|r2_hidden(esk4_2(X25,X31),X31)|X31=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.42  fof(c_0_18, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k1_relset_1(X40,X41,X42)=k1_relat_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.42  fof(c_0_19, negated_conjecture, (~v1_xboole_0(esk8_0)&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk7_0,esk8_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))&((v1_funct_1(esk10_0)&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk6_0))))&(m1_subset_1(esk11_0,esk7_0)&(r1_tarski(k2_relset_1(esk7_0,esk8_0,esk9_0),k1_relset_1(esk8_0,esk6_0,esk10_0))&(esk7_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0)!=k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.19/0.42  fof(c_0_20, plain, ![X43, X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k2_relset_1(X43,X44,X45)=k2_relat_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.42  cnf(c_0_21, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  fof(c_0_22, plain, ![X46, X47, X48]:((((~v1_funct_2(X48,X46,X47)|X46=k1_relset_1(X46,X47,X48)|X47=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X46!=k1_relset_1(X46,X47,X48)|v1_funct_2(X48,X46,X47)|X47=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))&((~v1_funct_2(X48,X46,X47)|X46=k1_relset_1(X46,X47,X48)|X46!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X46!=k1_relset_1(X46,X47,X48)|v1_funct_2(X48,X46,X47)|X46!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))))&((~v1_funct_2(X48,X46,X47)|X48=k1_xboole_0|X46=k1_xboole_0|X47!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X48!=k1_xboole_0|v1_funct_2(X48,X46,X47)|X46=k1_xboole_0|X47!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.42  cnf(c_0_23, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  fof(c_0_25, plain, ![X21, X22]:(~v1_relat_1(X21)|(~m1_subset_1(X22,k1_zfmisc_1(X21))|v1_relat_1(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.42  fof(c_0_26, plain, ![X23, X24]:v1_relat_1(k2_zfmisc_1(X23,X24)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.42  fof(c_0_27, plain, ![X19, X20]:(~m1_subset_1(X19,X20)|(v1_xboole_0(X20)|r2_hidden(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.42  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_29, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_30, plain, (r2_hidden(X1,k2_relat_1(X2))|X1!=k1_funct_1(X2,X3)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X3,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_31, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_32, negated_conjecture, (k1_relset_1(esk7_0,esk8_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_34, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_35, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  fof(c_0_36, plain, ![X17]:(~v1_xboole_0(X17)|X17=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.42  cnf(c_0_37, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk11_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  fof(c_0_39, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.42  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_relset_1(esk7_0,esk8_0,esk9_0),k1_relset_1(esk8_0,esk6_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_41, negated_conjecture, (k1_relset_1(esk8_0,esk6_0,esk10_0)=k1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_23, c_0_28])).
% 0.19/0.42  cnf(c_0_42, negated_conjecture, (k2_relset_1(esk7_0,esk8_0,esk9_0)=k2_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_29, c_0_24])).
% 0.19/0.42  cnf(c_0_43, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[c_0_30])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk9_0)=esk7_0|esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_24]), c_0_32]), c_0_33])])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_24]), c_0_35])])).
% 0.19/0.42  cnf(c_0_47, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.42  cnf(c_0_48, negated_conjecture, (r2_hidden(esk11_0,esk7_0)|v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.42  cnf(c_0_49, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  fof(c_0_50, plain, ![X52, X53, X54, X55, X56, X57]:(v1_xboole_0(X54)|(~v1_funct_1(X55)|~v1_funct_2(X55,X53,X54)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))|(~v1_funct_1(X56)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X52)))|(~m1_subset_1(X57,X53)|(~r1_tarski(k2_relset_1(X53,X54,X55),k1_relset_1(X54,X52,X56))|(X53=k1_xboole_0|k1_funct_1(k8_funct_2(X53,X54,X52,X55,X56),X57)=k1_funct_1(X56,k1_funct_1(X55,X57)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.19/0.42  cnf(c_0_51, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_relat_1(esk9_0),k1_relat_1(esk10_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(k1_funct_1(esk9_0,X1),k2_relat_1(esk9_0))|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (r2_hidden(esk11_0,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.19/0.42  cnf(c_0_55, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.42  cnf(c_0_56, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  fof(c_0_58, plain, ![X49, X50, X51]:(~v1_relat_1(X50)|~v5_relat_1(X50,X49)|~v1_funct_1(X50)|(~r2_hidden(X51,k1_relat_1(X50))|k7_partfun1(X49,X50,X51)=k1_funct_1(X50,X51))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.19/0.42  cnf(c_0_59, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk10_0))|~r2_hidden(X1,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.42  cnf(c_0_60, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(k1_funct_1(esk9_0,esk11_0),k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.42  fof(c_0_61, plain, ![X37, X38, X39]:((v4_relat_1(X39,X37)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(v5_relat_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.42  cnf(c_0_62, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk8_0,esk6_0,X2,esk10_0),X3)=k1_funct_1(esk10_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~v1_funct_2(X2,X1,esk8_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk8_0)))|~m1_subset_1(X3,X1)|~r1_tarski(k2_relset_1(X1,esk8_0,X2),k1_relat_1(esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_28]), c_0_56]), c_0_41])]), c_0_57])).
% 0.19/0.42  cnf(c_0_63, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.42  cnf(c_0_64, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(k1_funct_1(esk9_0,esk11_0),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (v1_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_28]), c_0_35])])).
% 0.19/0.42  cnf(c_0_66, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),X1)=k1_funct_1(esk10_0,k1_funct_1(esk9_0,X1))|~m1_subset_1(X1,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_33]), c_0_45]), c_0_24]), c_0_42]), c_0_52])]), c_0_49])).
% 0.19/0.42  fof(c_0_68, plain, ![X35, X36]:(~r2_hidden(X35,X36)|~r1_tarski(X36,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.42  fof(c_0_69, plain, ![X18]:r1_tarski(k1_xboole_0,X18), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (k7_partfun1(X1,esk10_0,k1_funct_1(esk9_0,esk11_0))=k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0))|esk8_0=k1_xboole_0|~v5_relat_1(esk10_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_56]), c_0_65])])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, (v5_relat_1(esk10_0,esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_28])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0)!=k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_73, negated_conjecture, (k1_funct_1(k8_funct_2(esk7_0,esk8_0,esk6_0,esk9_0,esk10_0),esk11_0)=k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0))), inference(spm,[status(thm)],[c_0_67, c_0_38])).
% 0.19/0.42  cnf(c_0_74, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.42  cnf(c_0_75, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.42  fof(c_0_76, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, (k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0))=k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0))|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (k7_partfun1(esk6_0,esk10_0,k1_funct_1(esk9_0,esk11_0))!=k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk11_0))), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.42  cnf(c_0_79, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.42  cnf(c_0_80, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.42  cnf(c_0_81, negated_conjecture, (esk8_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.42  cnf(c_0_82, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.42  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_81]), c_0_82])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 84
% 0.19/0.42  # Proof object clause steps            : 51
% 0.19/0.42  # Proof object formula steps           : 33
% 0.19/0.42  # Proof object conjectures             : 35
% 0.19/0.42  # Proof object clause conjectures      : 32
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 25
% 0.19/0.42  # Proof object initial formulas used   : 16
% 0.19/0.42  # Proof object generating inferences   : 22
% 0.19/0.42  # Proof object simplifying inferences  : 31
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 16
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 39
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 39
% 0.19/0.42  # Processed clauses                    : 499
% 0.19/0.42  # ...of these trivial                  : 0
% 0.19/0.42  # ...subsumed                          : 143
% 0.19/0.42  # ...remaining for further processing  : 356
% 0.19/0.42  # Other redundant clauses eliminated   : 0
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 7
% 0.19/0.42  # Backward-rewritten                   : 187
% 0.19/0.42  # Generated clauses                    : 625
% 0.19/0.42  # ...of the previous two non-trivial   : 643
% 0.19/0.42  # Contextual simplify-reflections      : 12
% 0.19/0.42  # Paramodulations                      : 607
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 17
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 122
% 0.19/0.42  #    Positive orientable unit clauses  : 14
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 6
% 0.19/0.42  #    Non-unit-clauses                  : 102
% 0.19/0.42  # Current number of unprocessed clauses: 201
% 0.19/0.42  # ...number of literals in the above   : 1026
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 234
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 11935
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 2729
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 150
% 0.19/0.42  # Unit Clause-clause subsumption calls : 76
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 7
% 0.19/0.42  # BW rewrite match successes           : 4
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 20963
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.086 s
% 0.19/0.42  # System time              : 0.000 s
% 0.19/0.42  # Total time               : 0.086 s
% 0.19/0.42  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
