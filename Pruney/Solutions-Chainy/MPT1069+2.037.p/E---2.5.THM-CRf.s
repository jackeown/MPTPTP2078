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
% DateTime   : Thu Dec  3 11:07:54 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 200 expanded)
%              Number of clauses        :   54 (  79 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  259 (1098 expanded)
%              Number of equality atoms :   66 ( 234 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k2_relset_1(X44,X45,X46) = k2_relat_1(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_17,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0)
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & v1_funct_1(esk8_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))
    & m1_subset_1(esk9_0,esk5_0)
    & r1_tarski(k2_relset_1(esk5_0,esk6_0,esk7_0),k1_relset_1(esk6_0,esk4_0,esk8_0))
    & esk5_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk5_0,esk6_0,esk4_0,esk7_0,esk8_0),esk9_0) != k7_partfun1(esk4_0,esk8_0,k1_funct_1(esk7_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_18,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X47,X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))
      | ~ r1_tarski(k2_relat_1(X50),X48)
      | m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X48))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk5_0,esk6_0,esk7_0),k1_relset_1(esk6_0,esk4_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k2_relset_1(esk5_0,esk6_0,esk7_0) = k2_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k1_relset_1(X41,X42,X43) = k1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_24,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | v1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),k1_relset_1(esk6_0,esk4_0,esk8_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v5_relat_1(X31,X30)
      | ~ v1_funct_1(X31)
      | ~ r2_hidden(X32,k1_relat_1(X31))
      | r2_hidden(k1_funct_1(X31,X32),X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

cnf(c_0_28,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X38,X39,X40] :
      ( ( v4_relat_1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v5_relat_1(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relset_1(esk6_0,esk4_0,esk8_0))))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_relset_1(esk5_0,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_36,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_relset_1(esk6_0,esk4_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_19])).

fof(c_0_38,plain,(
    ! [X51,X52,X53] :
      ( ( ~ v1_funct_2(X53,X51,X52)
        | X51 = k1_relset_1(X51,X52,X53)
        | X52 = k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X51 != k1_relset_1(X51,X52,X53)
        | v1_funct_2(X53,X51,X52)
        | X52 = k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( ~ v1_funct_2(X53,X51,X52)
        | X51 = k1_relset_1(X51,X52,X53)
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X51 != k1_relset_1(X51,X52,X53)
        | v1_funct_2(X53,X51,X52)
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( ~ v1_funct_2(X53,X51,X52)
        | X53 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X53 != k1_xboole_0
        | v1_funct_2(X53,X51,X52)
        | X51 = k1_xboole_0
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_39,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_40,plain,(
    ! [X17] :
      ( X17 = k1_xboole_0
      | r2_hidden(esk3_1(X17),X17) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_41,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_42,plain,(
    ! [X57,X58,X59,X60,X61,X62] :
      ( v1_xboole_0(X59)
      | ~ v1_funct_1(X60)
      | ~ v1_funct_2(X60,X58,X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
      | ~ v1_funct_1(X61)
      | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57)))
      | ~ m1_subset_1(X62,X58)
      | ~ r1_tarski(k2_relset_1(X58,X59,X60),k1_relset_1(X59,X57,X61))
      | X58 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X58,X59,X57,X60,X61),X62) = k1_funct_1(X61,k1_funct_1(X60,X62)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

fof(c_0_43,plain,(
    ! [X54,X55,X56] :
      ( ~ v1_relat_1(X55)
      | ~ v5_relat_1(X55,X54)
      | ~ v1_funct_1(X55)
      | ~ r2_hidden(X56,k1_relat_1(X55))
      | k7_partfun1(X54,X55,X56) = k1_funct_1(X55,X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),X2)
    | ~ v5_relat_1(esk7_0,X2)
    | ~ r2_hidden(X1,k1_relset_1(esk5_0,esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_46,negated_conjecture,
    ( v5_relat_1(esk7_0,k1_relset_1(esk6_0,esk4_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk9_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_relset_1(esk6_0,esk4_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),k1_relset_1(esk6_0,esk4_0,esk8_0))
    | ~ r2_hidden(X1,k1_relset_1(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_19]),c_0_48])])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk9_0,esk5_0)
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_64,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk6_0,esk4_0,X2,esk8_0),X3) = k1_funct_1(esk8_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk6_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk6_0)))
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(k2_relset_1(X1,esk6_0,X2),k1_relset_1(esk6_0,esk4_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_44]),c_0_54])]),c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( k7_partfun1(X1,esk8_0,X2) = k1_funct_1(esk8_0,X2)
    | ~ v5_relat_1(esk8_0,X1)
    | ~ r2_hidden(X2,k1_relset_1(esk6_0,esk4_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_54]),c_0_58])])).

cnf(c_0_66,negated_conjecture,
    ( v5_relat_1(esk8_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_44])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,X1),k1_relset_1(esk6_0,esk4_0,esk8_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk9_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk5_0,esk6_0,esk4_0,esk7_0,esk8_0),X1) = k1_funct_1(esk8_0,k1_funct_1(esk7_0,X1))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_48]),c_0_34]),c_0_19]),c_0_22]),c_0_26])]),c_0_63])).

fof(c_0_70,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | ~ r1_tarski(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_71,plain,(
    ! [X19] : r1_tarski(k1_xboole_0,X19) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_72,negated_conjecture,
    ( k7_partfun1(esk4_0,esk8_0,X1) = k1_funct_1(esk8_0,X1)
    | ~ r2_hidden(X1,k1_relset_1(esk6_0,esk4_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,esk9_0),k1_relset_1(esk6_0,esk4_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk5_0,esk6_0,esk4_0,esk7_0,esk8_0),esk9_0) != k7_partfun1(esk4_0,esk8_0,k1_funct_1(esk7_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_75,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk5_0,esk6_0,esk4_0,esk7_0,esk8_0),esk9_0) = k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_52])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k7_partfun1(esk4_0,esk8_0,k1_funct_1(esk7_0,esk9_0)) = k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk9_0))
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k7_partfun1(esk4_0,esk8_0,k1_funct_1(esk7_0,esk9_0)) != k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk9_0)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_82,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_82]),c_0_83])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:42:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.20/0.40  # and selection function SelectNewComplexAHP.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.029 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 0.20/0.40  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.40  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 0.20/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.40  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 0.20/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.40  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.40  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 0.20/0.40  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 0.20/0.40  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.40  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.20/0.40  fof(c_0_16, plain, ![X44, X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|k2_relset_1(X44,X45,X46)=k2_relat_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.40  fof(c_0_17, negated_conjecture, (~v1_xboole_0(esk6_0)&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&((v1_funct_1(esk8_0)&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))))&(m1_subset_1(esk9_0,esk5_0)&(r1_tarski(k2_relset_1(esk5_0,esk6_0,esk7_0),k1_relset_1(esk6_0,esk4_0,esk8_0))&(esk5_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk5_0,esk6_0,esk4_0,esk7_0,esk8_0),esk9_0)!=k7_partfun1(esk4_0,esk8_0,k1_funct_1(esk7_0,esk9_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.40  cnf(c_0_18, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  fof(c_0_20, plain, ![X47, X48, X49, X50]:(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))|(~r1_tarski(k2_relat_1(X50),X48)|m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X48))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 0.20/0.40  cnf(c_0_21, negated_conjecture, (r1_tarski(k2_relset_1(esk5_0,esk6_0,esk7_0),k1_relset_1(esk6_0,esk4_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (k2_relset_1(esk5_0,esk6_0,esk7_0)=k2_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.40  fof(c_0_23, plain, ![X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k1_relset_1(X41,X42,X43)=k1_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.40  fof(c_0_24, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|v1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.40  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),k1_relset_1(esk6_0,esk4_0,esk8_0))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.40  fof(c_0_27, plain, ![X30, X31, X32]:(~v1_relat_1(X31)|~v5_relat_1(X31,X30)|~v1_funct_1(X31)|(~r2_hidden(X32,k1_relat_1(X31))|r2_hidden(k1_funct_1(X31,X32),X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 0.20/0.40  cnf(c_0_28, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_29, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  fof(c_0_30, plain, ![X38, X39, X40]:((v4_relat_1(X40,X38)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(v5_relat_1(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relset_1(esk6_0,esk4_0,esk8_0))))|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.40  cnf(c_0_32, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (k1_relat_1(esk7_0)=k1_relset_1(esk5_0,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_19])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_19])).
% 0.20/0.40  cnf(c_0_36, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_relset_1(esk6_0,esk4_0,esk8_0))))), inference(spm,[status(thm)],[c_0_31, c_0_19])).
% 0.20/0.40  fof(c_0_38, plain, ![X51, X52, X53]:((((~v1_funct_2(X53,X51,X52)|X51=k1_relset_1(X51,X52,X53)|X52=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X51!=k1_relset_1(X51,X52,X53)|v1_funct_2(X53,X51,X52)|X52=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&((~v1_funct_2(X53,X51,X52)|X51=k1_relset_1(X51,X52,X53)|X51!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X51!=k1_relset_1(X51,X52,X53)|v1_funct_2(X53,X51,X52)|X51!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))&((~v1_funct_2(X53,X51,X52)|X53=k1_xboole_0|X51=k1_xboole_0|X52!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X53!=k1_xboole_0|v1_funct_2(X53,X51,X52)|X51=k1_xboole_0|X52!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.40  fof(c_0_39, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.40  fof(c_0_40, plain, ![X17]:(X17=k1_xboole_0|r2_hidden(esk3_1(X17),X17)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.40  fof(c_0_41, plain, ![X23, X24]:(~m1_subset_1(X23,X24)|(v1_xboole_0(X24)|r2_hidden(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.40  fof(c_0_42, plain, ![X57, X58, X59, X60, X61, X62]:(v1_xboole_0(X59)|(~v1_funct_1(X60)|~v1_funct_2(X60,X58,X59)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))|(~v1_funct_1(X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57)))|(~m1_subset_1(X62,X58)|(~r1_tarski(k2_relset_1(X58,X59,X60),k1_relset_1(X59,X57,X61))|(X58=k1_xboole_0|k1_funct_1(k8_funct_2(X58,X59,X57,X60,X61),X62)=k1_funct_1(X61,k1_funct_1(X60,X62)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.20/0.40  fof(c_0_43, plain, ![X54, X55, X56]:(~v1_relat_1(X55)|~v5_relat_1(X55,X54)|~v1_funct_1(X55)|(~r2_hidden(X56,k1_relat_1(X55))|k7_partfun1(X54,X55,X56)=k1_funct_1(X55,X56))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),X2)|~v5_relat_1(esk7_0,X2)|~r2_hidden(X1,k1_relset_1(esk5_0,esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (v5_relat_1(esk7_0,k1_relset_1(esk6_0,esk4_0,esk8_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.40  cnf(c_0_47, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_49, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_50, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.40  cnf(c_0_51, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk9_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_53, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_56, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (k1_relat_1(esk8_0)=k1_relset_1(esk6_0,esk4_0,esk8_0)), inference(spm,[status(thm)],[c_0_28, c_0_44])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_44])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),k1_relset_1(esk6_0,esk4_0,esk8_0))|~r2_hidden(X1,k1_relset_1(esk5_0,esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_19]), c_0_48])])).
% 0.20/0.40  cnf(c_0_61, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (r2_hidden(esk9_0,esk5_0)|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk6_0,esk4_0,X2,esk8_0),X3)=k1_funct_1(esk8_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~v1_funct_2(X2,X1,esk6_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk6_0)))|~m1_subset_1(X3,X1)|~r1_tarski(k2_relset_1(X1,esk6_0,X2),k1_relset_1(esk6_0,esk4_0,esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_44]), c_0_54])]), c_0_55])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (k7_partfun1(X1,esk8_0,X2)=k1_funct_1(esk8_0,X2)|~v5_relat_1(esk8_0,X1)|~r2_hidden(X2,k1_relset_1(esk6_0,esk4_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_54]), c_0_58])])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (v5_relat_1(esk8_0,esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_44])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,X1),k1_relset_1(esk6_0,esk4_0,esk8_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (r2_hidden(esk9_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (k1_funct_1(k8_funct_2(esk5_0,esk6_0,esk4_0,esk7_0,esk8_0),X1)=k1_funct_1(esk8_0,k1_funct_1(esk7_0,X1))|~m1_subset_1(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_48]), c_0_34]), c_0_19]), c_0_22]), c_0_26])]), c_0_63])).
% 0.20/0.40  fof(c_0_70, plain, ![X33, X34]:(~r2_hidden(X33,X34)|~r1_tarski(X34,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.40  fof(c_0_71, plain, ![X19]:r1_tarski(k1_xboole_0,X19), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.40  cnf(c_0_72, negated_conjecture, (k7_partfun1(esk4_0,esk8_0,X1)=k1_funct_1(esk8_0,X1)|~r2_hidden(X1,k1_relset_1(esk6_0,esk4_0,esk8_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.40  cnf(c_0_73, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,esk9_0),k1_relset_1(esk6_0,esk4_0,esk8_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, (k1_funct_1(k8_funct_2(esk5_0,esk6_0,esk4_0,esk7_0,esk8_0),esk9_0)!=k7_partfun1(esk4_0,esk8_0,k1_funct_1(esk7_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (k1_funct_1(k8_funct_2(esk5_0,esk6_0,esk4_0,esk7_0,esk8_0),esk9_0)=k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk9_0))), inference(spm,[status(thm)],[c_0_69, c_0_52])).
% 0.20/0.40  cnf(c_0_76, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.40  cnf(c_0_77, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.40  cnf(c_0_78, negated_conjecture, (k7_partfun1(esk4_0,esk8_0,k1_funct_1(esk7_0,esk9_0))=k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk9_0))|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.40  cnf(c_0_79, negated_conjecture, (k7_partfun1(esk4_0,esk8_0,k1_funct_1(esk7_0,esk9_0))!=k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk9_0))), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.40  cnf(c_0_80, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.40  cnf(c_0_81, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_82, negated_conjecture, (esk6_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.40  cnf(c_0_83, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.40  cnf(c_0_84, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_82]), c_0_83])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 85
% 0.20/0.40  # Proof object clause steps            : 54
% 0.20/0.40  # Proof object formula steps           : 31
% 0.20/0.40  # Proof object conjectures             : 39
% 0.20/0.40  # Proof object clause conjectures      : 36
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 25
% 0.20/0.40  # Proof object initial formulas used   : 15
% 0.20/0.40  # Proof object generating inferences   : 25
% 0.20/0.40  # Proof object simplifying inferences  : 24
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 20
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 39
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 39
% 0.20/0.40  # Processed clauses                    : 357
% 0.20/0.40  # ...of these trivial                  : 2
% 0.20/0.40  # ...subsumed                          : 78
% 0.20/0.40  # ...remaining for further processing  : 277
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 152
% 0.20/0.40  # Generated clauses                    : 347
% 0.20/0.40  # ...of the previous two non-trivial   : 435
% 0.20/0.40  # Contextual simplify-reflections      : 4
% 0.20/0.40  # Paramodulations                      : 339
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 7
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 85
% 0.20/0.40  #    Positive orientable unit clauses  : 18
% 0.20/0.40  #    Positive unorientable unit clauses: 2
% 0.20/0.40  #    Negative unit clauses             : 4
% 0.20/0.40  #    Non-unit-clauses                  : 61
% 0.20/0.40  # Current number of unprocessed clauses: 46
% 0.20/0.40  # ...number of literals in the above   : 134
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 192
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 3434
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 1956
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 64
% 0.20/0.40  # Unit Clause-clause subsumption calls : 169
% 0.20/0.40  # Rewrite failures with RHS unbound    : 24
% 0.20/0.40  # BW rewrite match attempts            : 22
% 0.20/0.40  # BW rewrite match successes           : 7
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 9760
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.051 s
% 0.20/0.40  # System time              : 0.006 s
% 0.20/0.40  # Total time               : 0.057 s
% 0.20/0.40  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
