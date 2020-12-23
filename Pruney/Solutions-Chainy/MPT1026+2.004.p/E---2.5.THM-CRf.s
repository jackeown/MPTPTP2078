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
% DateTime   : Thu Dec  3 11:06:44 EST 2020

% Result     : Theorem 0.44s
% Output     : CNFRefutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 435 expanded)
%              Number of clauses        :   73 ( 219 expanded)
%              Number of leaves         :   19 (  97 expanded)
%              Depth                    :   15
%              Number of atoms          :  335 (3098 expanded)
%              Number of equality atoms :   71 (1127 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(t121_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t194_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(c_0_19,plain,(
    ! [X50,X51,X52,X53,X55,X56,X57,X58,X59,X61] :
      ( ( v1_relat_1(esk4_4(X50,X51,X52,X53))
        | ~ r2_hidden(X53,X52)
        | X52 != k1_funct_2(X50,X51) )
      & ( v1_funct_1(esk4_4(X50,X51,X52,X53))
        | ~ r2_hidden(X53,X52)
        | X52 != k1_funct_2(X50,X51) )
      & ( X53 = esk4_4(X50,X51,X52,X53)
        | ~ r2_hidden(X53,X52)
        | X52 != k1_funct_2(X50,X51) )
      & ( k1_relat_1(esk4_4(X50,X51,X52,X53)) = X50
        | ~ r2_hidden(X53,X52)
        | X52 != k1_funct_2(X50,X51) )
      & ( r1_tarski(k2_relat_1(esk4_4(X50,X51,X52,X53)),X51)
        | ~ r2_hidden(X53,X52)
        | X52 != k1_funct_2(X50,X51) )
      & ( ~ v1_relat_1(X56)
        | ~ v1_funct_1(X56)
        | X55 != X56
        | k1_relat_1(X56) != X50
        | ~ r1_tarski(k2_relat_1(X56),X51)
        | r2_hidden(X55,X52)
        | X52 != k1_funct_2(X50,X51) )
      & ( ~ r2_hidden(esk5_3(X57,X58,X59),X59)
        | ~ v1_relat_1(X61)
        | ~ v1_funct_1(X61)
        | esk5_3(X57,X58,X59) != X61
        | k1_relat_1(X61) != X57
        | ~ r1_tarski(k2_relat_1(X61),X58)
        | X59 = k1_funct_2(X57,X58) )
      & ( v1_relat_1(esk6_3(X57,X58,X59))
        | r2_hidden(esk5_3(X57,X58,X59),X59)
        | X59 = k1_funct_2(X57,X58) )
      & ( v1_funct_1(esk6_3(X57,X58,X59))
        | r2_hidden(esk5_3(X57,X58,X59),X59)
        | X59 = k1_funct_2(X57,X58) )
      & ( esk5_3(X57,X58,X59) = esk6_3(X57,X58,X59)
        | r2_hidden(esk5_3(X57,X58,X59),X59)
        | X59 = k1_funct_2(X57,X58) )
      & ( k1_relat_1(esk6_3(X57,X58,X59)) = X57
        | r2_hidden(esk5_3(X57,X58,X59),X59)
        | X59 = k1_funct_2(X57,X58) )
      & ( r1_tarski(k2_relat_1(esk6_3(X57,X58,X59)),X58)
        | r2_hidden(esk5_3(X57,X58,X59),X59)
        | X59 = k1_funct_2(X57,X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_20,plain,
    ( v1_relat_1(esk4_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_21,plain,
    ( X1 = esk4_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_23,plain,
    ( v1_funct_1(esk4_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( v1_relat_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( esk4_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_26,negated_conjecture,
    ( r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))
    & ( ~ v1_funct_1(esk9_0)
      | ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
      | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_27,plain,
    ( v1_funct_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X63] :
      ( ( v1_funct_1(X63)
        | ~ v1_relat_1(X63)
        | ~ v1_funct_1(X63) )
      & ( v1_funct_2(X63,k1_relat_1(X63),k2_relat_1(X63))
        | ~ v1_relat_1(X63)
        | ~ v1_funct_1(X63) )
      & ( m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X63),k2_relat_1(X63))))
        | ~ v1_relat_1(X63)
        | ~ v1_funct_1(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

fof(c_0_32,plain,(
    ! [X35] :
      ( ( k1_relat_1(X35) != k1_xboole_0
        | k2_relat_1(X35) = k1_xboole_0
        | ~ v1_relat_1(X35) )
      & ( k2_relat_1(X35) != k1_xboole_0
        | k1_relat_1(X35) = k1_xboole_0
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

fof(c_0_33,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_34,plain,(
    ! [X16] : r1_tarski(k1_xboole_0,X16) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_38,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X28,X29] : v1_relat_1(k2_zfmisc_1(X28,X29)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X30,X31] : r1_tarski(k2_relat_1(k2_zfmisc_1(X30,X31)),X31) ),
    inference(variable_rename,[status(thm)],[t194_relat_1])).

fof(c_0_43,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk9_0),k2_relat_1(esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_45,negated_conjecture,
    ( k2_relat_1(esk9_0) = k1_xboole_0
    | k1_relat_1(esk9_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_36])).

cnf(c_0_46,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_51,plain,(
    ! [X33,X34] :
      ( ( r1_tarski(k1_relat_1(X33),k1_relat_1(X34))
        | ~ r1_tarski(X33,X34)
        | ~ v1_relat_1(X34)
        | ~ v1_relat_1(X33) )
      & ( r1_tarski(k2_relat_1(X33),k2_relat_1(X34))
        | ~ r1_tarski(X33,X34)
        | ~ v1_relat_1(X34)
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk9_0),k1_xboole_0)))
    | k1_relat_1(esk9_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = k1_xboole_0
    | k2_relat_1(k2_zfmisc_1(X1,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_56,plain,(
    ! [X36,X37] :
      ( ~ r2_hidden(X36,X37)
      | ~ r1_tarski(X37,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_57,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,X20)
      | v1_xboole_0(X20)
      | r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_58,plain,(
    ! [X17] : m1_subset_1(esk3_1(X17),X17) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_59,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | ~ v1_xboole_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(k1_relat_1(esk9_0),k1_xboole_0))
    | k1_relat_1(esk9_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_64,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,plain,
    ( m1_subset_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_70,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_71,plain,(
    ! [X47,X48,X49] :
      ( ( v1_funct_1(X49)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | v1_xboole_0(X48) )
      & ( v1_partfun1(X49,X47)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | v1_xboole_0(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_72,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_73,plain,
    ( r1_tarski(k2_relat_1(esk4_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_74,plain,
    ( k1_relat_1(esk4_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk9_0),k1_xboole_0)
    | k1_relat_1(esk9_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_47]),c_0_36])])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_41])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_78,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_80,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_2(esk9_0,k1_relat_1(esk9_0),k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_36]),c_0_37])])).

cnf(c_0_82,plain,
    ( r1_tarski(k2_relat_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_83,plain,
    ( k1_relat_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_74])).

fof(c_0_84,plain,(
    ! [X44,X45,X46] :
      ( ~ v1_xboole_0(X44)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | v1_partfun1(X46,X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk9_0),k1_zfmisc_1(k1_xboole_0))
    | k1_relat_1(esk9_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_75])).

cnf(c_0_86,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_87,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( v1_partfun1(esk9_0,k1_relat_1(esk9_0))
    | v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_44]),c_0_81]),c_0_37])])).

fof(c_0_89,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X40)
      | ~ r1_tarski(k1_relat_1(X40),X38)
      | ~ r1_tarski(k2_relat_1(X40),X39)
      | m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_90,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_25])).

cnf(c_0_91,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_25])).

cnf(c_0_92,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( k1_relat_1(esk9_0) != k1_xboole_0
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_85]),c_0_86])])).

cnf(c_0_94,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0
    | k2_relat_1(esk9_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_36])).

cnf(c_0_95,negated_conjecture,
    ( k2_relat_1(esk9_0) = k1_xboole_0
    | v1_partfun1(esk9_0,k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

fof(c_0_96,plain,(
    ! [X41,X42,X43] :
      ( ( v1_funct_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v1_partfun1(X43,X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( v1_funct_2(X43,X41,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_partfun1(X43,X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_97,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_30])).

cnf(c_0_99,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_30])).

cnf(c_0_100,negated_conjecture,
    ( v1_partfun1(esk9_0,k1_relat_1(esk9_0))
    | ~ v1_xboole_0(k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_44])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk9_0))
    | k1_relat_1(esk9_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_93,c_0_77])).

cnf(c_0_102,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0
    | v1_partfun1(esk9_0,k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( ~ v1_funct_1(esk9_0)
    | ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_104,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk8_0)))
    | ~ r1_tarski(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_36]),c_0_99])])).

cnf(c_0_106,negated_conjecture,
    ( v1_partfun1(esk9_0,k1_relat_1(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_37])])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_2(esk9_0,X1,esk8_0)
    | ~ v1_partfun1(esk9_0,X1)
    | ~ r1_tarski(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_37])])).

cnf(c_0_109,negated_conjecture,
    ( v1_partfun1(esk9_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_106,c_0_99])).

cnf(c_0_110,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_105]),c_0_61])])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_61])]),c_0_110]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:02:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.44/0.59  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S04AN
% 0.44/0.59  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.44/0.59  #
% 0.44/0.59  # Preprocessing time       : 0.029 s
% 0.44/0.59  # Presaturation interreduction done
% 0.44/0.59  
% 0.44/0.59  # Proof found!
% 0.44/0.59  # SZS status Theorem
% 0.44/0.59  # SZS output start CNFRefutation
% 0.44/0.59  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.44/0.59  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.44/0.59  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.44/0.59  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.44/0.59  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.44/0.59  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.44/0.59  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.44/0.59  fof(t194_relat_1, axiom, ![X1, X2]:r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 0.44/0.59  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.44/0.59  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.44/0.59  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.44/0.59  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.44/0.59  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.44/0.59  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.44/0.59  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.44/0.59  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.44/0.59  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.44/0.59  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.44/0.59  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.44/0.59  fof(c_0_19, plain, ![X50, X51, X52, X53, X55, X56, X57, X58, X59, X61]:(((((((v1_relat_1(esk4_4(X50,X51,X52,X53))|~r2_hidden(X53,X52)|X52!=k1_funct_2(X50,X51))&(v1_funct_1(esk4_4(X50,X51,X52,X53))|~r2_hidden(X53,X52)|X52!=k1_funct_2(X50,X51)))&(X53=esk4_4(X50,X51,X52,X53)|~r2_hidden(X53,X52)|X52!=k1_funct_2(X50,X51)))&(k1_relat_1(esk4_4(X50,X51,X52,X53))=X50|~r2_hidden(X53,X52)|X52!=k1_funct_2(X50,X51)))&(r1_tarski(k2_relat_1(esk4_4(X50,X51,X52,X53)),X51)|~r2_hidden(X53,X52)|X52!=k1_funct_2(X50,X51)))&(~v1_relat_1(X56)|~v1_funct_1(X56)|X55!=X56|k1_relat_1(X56)!=X50|~r1_tarski(k2_relat_1(X56),X51)|r2_hidden(X55,X52)|X52!=k1_funct_2(X50,X51)))&((~r2_hidden(esk5_3(X57,X58,X59),X59)|(~v1_relat_1(X61)|~v1_funct_1(X61)|esk5_3(X57,X58,X59)!=X61|k1_relat_1(X61)!=X57|~r1_tarski(k2_relat_1(X61),X58))|X59=k1_funct_2(X57,X58))&(((((v1_relat_1(esk6_3(X57,X58,X59))|r2_hidden(esk5_3(X57,X58,X59),X59)|X59=k1_funct_2(X57,X58))&(v1_funct_1(esk6_3(X57,X58,X59))|r2_hidden(esk5_3(X57,X58,X59),X59)|X59=k1_funct_2(X57,X58)))&(esk5_3(X57,X58,X59)=esk6_3(X57,X58,X59)|r2_hidden(esk5_3(X57,X58,X59),X59)|X59=k1_funct_2(X57,X58)))&(k1_relat_1(esk6_3(X57,X58,X59))=X57|r2_hidden(esk5_3(X57,X58,X59),X59)|X59=k1_funct_2(X57,X58)))&(r1_tarski(k2_relat_1(esk6_3(X57,X58,X59)),X58)|r2_hidden(esk5_3(X57,X58,X59),X59)|X59=k1_funct_2(X57,X58))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.44/0.59  cnf(c_0_20, plain, (v1_relat_1(esk4_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.44/0.59  cnf(c_0_21, plain, (X1=esk4_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.44/0.59  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.44/0.59  cnf(c_0_23, plain, (v1_funct_1(esk4_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.44/0.59  cnf(c_0_24, plain, (v1_relat_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.44/0.59  cnf(c_0_25, plain, (esk4_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_21])).
% 0.44/0.59  fof(c_0_26, negated_conjecture, (r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))&(~v1_funct_1(esk9_0)|~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.44/0.59  cnf(c_0_27, plain, (v1_funct_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.44/0.59  fof(c_0_28, plain, ![X63]:(((v1_funct_1(X63)|(~v1_relat_1(X63)|~v1_funct_1(X63)))&(v1_funct_2(X63,k1_relat_1(X63),k2_relat_1(X63))|(~v1_relat_1(X63)|~v1_funct_1(X63))))&(m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X63),k2_relat_1(X63))))|(~v1_relat_1(X63)|~v1_funct_1(X63)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.44/0.59  cnf(c_0_29, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.44/0.59  cnf(c_0_30, negated_conjecture, (r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.44/0.59  cnf(c_0_31, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 0.44/0.59  fof(c_0_32, plain, ![X35]:((k1_relat_1(X35)!=k1_xboole_0|k2_relat_1(X35)=k1_xboole_0|~v1_relat_1(X35))&(k2_relat_1(X35)!=k1_xboole_0|k1_relat_1(X35)=k1_xboole_0|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.44/0.59  fof(c_0_33, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.44/0.60  fof(c_0_34, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.44/0.60  cnf(c_0_35, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.44/0.60  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.44/0.60  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk9_0)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.44/0.60  cnf(c_0_38, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.44/0.60  fof(c_0_39, plain, ![X28, X29]:v1_relat_1(k2_zfmisc_1(X28,X29)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.44/0.60  cnf(c_0_40, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.44/0.60  cnf(c_0_41, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.44/0.60  fof(c_0_42, plain, ![X30, X31]:r1_tarski(k2_relat_1(k2_zfmisc_1(X30,X31)),X31), inference(variable_rename,[status(thm)],[t194_relat_1])).
% 0.44/0.60  fof(c_0_43, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.44/0.60  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk9_0),k2_relat_1(esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.44/0.60  cnf(c_0_45, negated_conjecture, (k2_relat_1(esk9_0)=k1_xboole_0|k1_relat_1(esk9_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_36])).
% 0.44/0.60  cnf(c_0_46, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.44/0.60  cnf(c_0_47, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.44/0.60  cnf(c_0_48, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.44/0.60  cnf(c_0_49, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.44/0.60  cnf(c_0_50, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.44/0.60  fof(c_0_51, plain, ![X33, X34]:((r1_tarski(k1_relat_1(X33),k1_relat_1(X34))|~r1_tarski(X33,X34)|~v1_relat_1(X34)|~v1_relat_1(X33))&(r1_tarski(k2_relat_1(X33),k2_relat_1(X34))|~r1_tarski(X33,X34)|~v1_relat_1(X34)|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.44/0.60  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.44/0.60  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk9_0),k1_xboole_0)))|k1_relat_1(esk9_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.44/0.60  cnf(c_0_54, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=k1_xboole_0|k2_relat_1(k2_zfmisc_1(X1,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.44/0.60  cnf(c_0_55, plain, (k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.44/0.60  fof(c_0_56, plain, ![X36, X37]:(~r2_hidden(X36,X37)|~r1_tarski(X37,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.44/0.60  fof(c_0_57, plain, ![X19, X20]:(~m1_subset_1(X19,X20)|(v1_xboole_0(X20)|r2_hidden(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.44/0.60  fof(c_0_58, plain, ![X17]:m1_subset_1(esk3_1(X17),X17), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.44/0.60  fof(c_0_59, plain, ![X23, X24, X25]:(~r2_hidden(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X25))|~v1_xboole_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.44/0.60  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.44/0.60  cnf(c_0_61, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_50])).
% 0.44/0.60  cnf(c_0_62, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.44/0.60  cnf(c_0_63, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(k1_relat_1(esk9_0),k1_xboole_0))|k1_relat_1(esk9_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.44/0.60  cnf(c_0_64, plain, (k1_relat_1(k2_zfmisc_1(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.44/0.60  cnf(c_0_65, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.44/0.60  cnf(c_0_66, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.44/0.60  cnf(c_0_67, plain, (m1_subset_1(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.44/0.60  cnf(c_0_68, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.44/0.60  cnf(c_0_69, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.44/0.60  fof(c_0_70, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.44/0.60  fof(c_0_71, plain, ![X47, X48, X49]:((v1_funct_1(X49)|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|v1_xboole_0(X48))&(v1_partfun1(X49,X47)|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|v1_xboole_0(X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.44/0.60  cnf(c_0_72, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.44/0.60  cnf(c_0_73, plain, (r1_tarski(k2_relat_1(esk4_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.44/0.60  cnf(c_0_74, plain, (k1_relat_1(esk4_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.44/0.60  cnf(c_0_75, negated_conjecture, (r1_tarski(k1_relat_1(esk9_0),k1_xboole_0)|k1_relat_1(esk9_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_47]), c_0_36])])).
% 0.44/0.60  cnf(c_0_76, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_41])).
% 0.44/0.60  cnf(c_0_77, plain, (v1_xboole_0(X1)|r2_hidden(esk3_1(X1),X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.44/0.60  cnf(c_0_78, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.44/0.60  cnf(c_0_79, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.44/0.60  cnf(c_0_80, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.44/0.60  cnf(c_0_81, negated_conjecture, (v1_funct_2(esk9_0,k1_relat_1(esk9_0),k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_36]), c_0_37])])).
% 0.44/0.60  cnf(c_0_82, plain, (r1_tarski(k2_relat_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_73])).
% 0.44/0.60  cnf(c_0_83, plain, (k1_relat_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_74])).
% 0.44/0.60  fof(c_0_84, plain, ![X44, X45, X46]:(~v1_xboole_0(X44)|(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|v1_partfun1(X46,X44))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.44/0.60  cnf(c_0_85, negated_conjecture, (m1_subset_1(k1_relat_1(esk9_0),k1_zfmisc_1(k1_xboole_0))|k1_relat_1(esk9_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_75])).
% 0.44/0.60  cnf(c_0_86, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.44/0.60  cnf(c_0_87, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.44/0.60  cnf(c_0_88, negated_conjecture, (v1_partfun1(esk9_0,k1_relat_1(esk9_0))|v1_xboole_0(k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_44]), c_0_81]), c_0_37])])).
% 0.44/0.60  fof(c_0_89, plain, ![X38, X39, X40]:(~v1_relat_1(X40)|(~r1_tarski(k1_relat_1(X40),X38)|~r1_tarski(k2_relat_1(X40),X39)|m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.44/0.60  cnf(c_0_90, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_82, c_0_25])).
% 0.44/0.60  cnf(c_0_91, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_83, c_0_25])).
% 0.44/0.60  cnf(c_0_92, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.44/0.60  cnf(c_0_93, negated_conjecture, (k1_relat_1(esk9_0)!=k1_xboole_0|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_85]), c_0_86])])).
% 0.44/0.60  cnf(c_0_94, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0|k2_relat_1(esk9_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_36])).
% 0.44/0.60  cnf(c_0_95, negated_conjecture, (k2_relat_1(esk9_0)=k1_xboole_0|v1_partfun1(esk9_0,k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.44/0.60  fof(c_0_96, plain, ![X41, X42, X43]:((v1_funct_1(X43)|(~v1_funct_1(X43)|~v1_partfun1(X43,X41))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(v1_funct_2(X43,X41,X42)|(~v1_funct_1(X43)|~v1_partfun1(X43,X41))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.44/0.60  cnf(c_0_97, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.44/0.60  cnf(c_0_98, negated_conjecture, (r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_90, c_0_30])).
% 0.44/0.60  cnf(c_0_99, negated_conjecture, (k1_relat_1(esk9_0)=esk7_0), inference(spm,[status(thm)],[c_0_91, c_0_30])).
% 0.44/0.60  cnf(c_0_100, negated_conjecture, (v1_partfun1(esk9_0,k1_relat_1(esk9_0))|~v1_xboole_0(k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_92, c_0_44])).
% 0.44/0.60  cnf(c_0_101, negated_conjecture, (v1_xboole_0(k1_relat_1(esk9_0))|k1_relat_1(esk9_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_93, c_0_77])).
% 0.44/0.60  cnf(c_0_102, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0|v1_partfun1(esk9_0,k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.44/0.60  cnf(c_0_103, negated_conjecture, (~v1_funct_1(esk9_0)|~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.44/0.60  cnf(c_0_104, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.44/0.60  cnf(c_0_105, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk8_0)))|~r1_tarski(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_36]), c_0_99])])).
% 0.44/0.60  cnf(c_0_106, negated_conjecture, (v1_partfun1(esk9_0,k1_relat_1(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102])).
% 0.44/0.60  cnf(c_0_107, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_37])])).
% 0.44/0.60  cnf(c_0_108, negated_conjecture, (v1_funct_2(esk9_0,X1,esk8_0)|~v1_partfun1(esk9_0,X1)|~r1_tarski(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_37])])).
% 0.44/0.60  cnf(c_0_109, negated_conjecture, (v1_partfun1(esk9_0,esk7_0)), inference(rw,[status(thm)],[c_0_106, c_0_99])).
% 0.44/0.60  cnf(c_0_110, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_105]), c_0_61])])).
% 0.44/0.60  cnf(c_0_111, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_61])]), c_0_110]), ['proof']).
% 0.44/0.60  # SZS output end CNFRefutation
% 0.44/0.60  # Proof object total steps             : 112
% 0.44/0.60  # Proof object clause steps            : 73
% 0.44/0.60  # Proof object formula steps           : 39
% 0.44/0.60  # Proof object conjectures             : 30
% 0.44/0.60  # Proof object clause conjectures      : 27
% 0.44/0.60  # Proof object formula conjectures     : 3
% 0.44/0.60  # Proof object initial clauses used    : 28
% 0.44/0.60  # Proof object initial formulas used   : 19
% 0.44/0.60  # Proof object generating inferences   : 37
% 0.44/0.60  # Proof object simplifying inferences  : 33
% 0.44/0.60  # Training examples: 0 positive, 0 negative
% 0.44/0.60  # Parsed axioms                        : 22
% 0.44/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.44/0.60  # Initial clauses                      : 45
% 0.44/0.60  # Removed in clause preprocessing      : 3
% 0.44/0.60  # Initial clauses in saturation        : 42
% 0.44/0.60  # Processed clauses                    : 4106
% 0.44/0.60  # ...of these trivial                  : 27
% 0.44/0.60  # ...subsumed                          : 2932
% 0.44/0.60  # ...remaining for further processing  : 1147
% 0.44/0.60  # Other redundant clauses eliminated   : 11
% 0.44/0.60  # Clauses deleted for lack of memory   : 0
% 0.44/0.60  # Backward-subsumed                    : 109
% 0.44/0.60  # Backward-rewritten                   : 167
% 0.44/0.60  # Generated clauses                    : 12484
% 0.44/0.60  # ...of the previous two non-trivial   : 11107
% 0.44/0.60  # Contextual simplify-reflections      : 62
% 0.44/0.60  # Paramodulations                      : 12471
% 0.44/0.60  # Factorizations                       : 4
% 0.44/0.60  # Equation resolutions                 : 11
% 0.44/0.60  # Propositional unsat checks           : 0
% 0.44/0.60  #    Propositional check models        : 0
% 0.44/0.60  #    Propositional check unsatisfiable : 0
% 0.44/0.60  #    Propositional clauses             : 0
% 0.44/0.60  #    Propositional clauses after purity: 0
% 0.44/0.60  #    Propositional unsat core size     : 0
% 0.44/0.60  #    Propositional preprocessing time  : 0.000
% 0.44/0.60  #    Propositional encoding time       : 0.000
% 0.44/0.60  #    Propositional solver time         : 0.000
% 0.44/0.60  #    Success case prop preproc time    : 0.000
% 0.44/0.60  #    Success case prop encoding time   : 0.000
% 0.44/0.60  #    Success case prop solver time     : 0.000
% 0.44/0.60  # Current number of processed clauses  : 821
% 0.44/0.60  #    Positive orientable unit clauses  : 41
% 0.44/0.60  #    Positive unorientable unit clauses: 0
% 0.44/0.60  #    Negative unit clauses             : 18
% 0.44/0.60  #    Non-unit-clauses                  : 762
% 0.44/0.60  # Current number of unprocessed clauses: 6492
% 0.44/0.60  # ...number of literals in the above   : 24433
% 0.44/0.60  # Current number of archived formulas  : 0
% 0.44/0.60  # Current number of archived clauses   : 317
% 0.44/0.60  # Clause-clause subsumption calls (NU) : 83895
% 0.44/0.60  # Rec. Clause-clause subsumption calls : 47847
% 0.44/0.60  # Non-unit clause-clause subsumptions  : 2235
% 0.44/0.60  # Unit Clause-clause subsumption calls : 1195
% 0.44/0.60  # Rewrite failures with RHS unbound    : 0
% 0.44/0.60  # BW rewrite match attempts            : 26
% 0.44/0.60  # BW rewrite match successes           : 9
% 0.44/0.60  # Condensation attempts                : 0
% 0.44/0.60  # Condensation successes               : 0
% 0.44/0.60  # Termbank termtop insertions          : 149489
% 0.44/0.60  
% 0.44/0.60  # -------------------------------------------------
% 0.44/0.60  # User time                : 0.246 s
% 0.44/0.60  # System time              : 0.010 s
% 0.44/0.60  # Total time               : 0.256 s
% 0.44/0.60  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
