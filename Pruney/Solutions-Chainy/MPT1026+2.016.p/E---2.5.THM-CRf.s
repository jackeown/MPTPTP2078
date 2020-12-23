%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 673 expanded)
%              Number of clauses        :   73 ( 341 expanded)
%              Number of leaves         :   15 ( 147 expanded)
%              Depth                    :   15
%              Number of atoms          :  376 (5220 expanded)
%              Number of equality atoms :   57 (1910 expanded)
%              Maximal formula depth    :   25 (   5 average)
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

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t5_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( k1_relat_1(X3) = X1
          & ! [X4] :
              ( r2_hidden(X4,X1)
             => r2_hidden(k1_funct_1(X3,X4),X2) ) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

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

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(c_0_15,plain,(
    ! [X44,X45,X46,X47,X49,X50,X51,X52,X53,X55] :
      ( ( v1_relat_1(esk3_4(X44,X45,X46,X47))
        | ~ r2_hidden(X47,X46)
        | X46 != k1_funct_2(X44,X45) )
      & ( v1_funct_1(esk3_4(X44,X45,X46,X47))
        | ~ r2_hidden(X47,X46)
        | X46 != k1_funct_2(X44,X45) )
      & ( X47 = esk3_4(X44,X45,X46,X47)
        | ~ r2_hidden(X47,X46)
        | X46 != k1_funct_2(X44,X45) )
      & ( k1_relat_1(esk3_4(X44,X45,X46,X47)) = X44
        | ~ r2_hidden(X47,X46)
        | X46 != k1_funct_2(X44,X45) )
      & ( r1_tarski(k2_relat_1(esk3_4(X44,X45,X46,X47)),X45)
        | ~ r2_hidden(X47,X46)
        | X46 != k1_funct_2(X44,X45) )
      & ( ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50)
        | X49 != X50
        | k1_relat_1(X50) != X44
        | ~ r1_tarski(k2_relat_1(X50),X45)
        | r2_hidden(X49,X46)
        | X46 != k1_funct_2(X44,X45) )
      & ( ~ r2_hidden(esk4_3(X51,X52,X53),X53)
        | ~ v1_relat_1(X55)
        | ~ v1_funct_1(X55)
        | esk4_3(X51,X52,X53) != X55
        | k1_relat_1(X55) != X51
        | ~ r1_tarski(k2_relat_1(X55),X52)
        | X53 = k1_funct_2(X51,X52) )
      & ( v1_relat_1(esk5_3(X51,X52,X53))
        | r2_hidden(esk4_3(X51,X52,X53),X53)
        | X53 = k1_funct_2(X51,X52) )
      & ( v1_funct_1(esk5_3(X51,X52,X53))
        | r2_hidden(esk4_3(X51,X52,X53),X53)
        | X53 = k1_funct_2(X51,X52) )
      & ( esk4_3(X51,X52,X53) = esk5_3(X51,X52,X53)
        | r2_hidden(esk4_3(X51,X52,X53),X53)
        | X53 = k1_funct_2(X51,X52) )
      & ( k1_relat_1(esk5_3(X51,X52,X53)) = X51
        | r2_hidden(esk4_3(X51,X52,X53),X53)
        | X53 = k1_funct_2(X51,X52) )
      & ( r1_tarski(k2_relat_1(esk5_3(X51,X52,X53)),X52)
        | r2_hidden(esk4_3(X51,X52,X53),X53)
        | X53 = k1_funct_2(X51,X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_16,plain,
    ( k1_relat_1(esk3_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_17,plain,
    ( X1 = esk3_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_19,plain,
    ( v1_funct_1(esk3_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_relat_1(esk3_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( esk3_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_23,negated_conjecture,
    ( r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))
    & ( ~ v1_funct_1(esk9_0)
      | ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
      | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_24,plain,
    ( v1_funct_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( v1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X57] :
      ( ( v1_funct_1(X57)
        | ~ v1_relat_1(X57)
        | ~ v1_funct_1(X57) )
      & ( v1_funct_2(X57,k1_relat_1(X57),k2_relat_1(X57))
        | ~ v1_relat_1(X57)
        | ~ v1_funct_1(X57) )
      & ( m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X57),k2_relat_1(X57))))
        | ~ v1_relat_1(X57)
        | ~ v1_funct_1(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_27,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

fof(c_0_31,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_xboole_0(X26)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X26)))
      | v1_xboole_0(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_32,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_33,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_34,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | ~ v1_xboole_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_42,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_43,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X58,X59,X60] :
      ( ( v1_funct_1(X60)
        | r2_hidden(esk6_3(X58,X59,X60),X58)
        | k1_relat_1(X60) != X58
        | ~ v1_relat_1(X60)
        | ~ v1_funct_1(X60) )
      & ( v1_funct_2(X60,X58,X59)
        | r2_hidden(esk6_3(X58,X59,X60),X58)
        | k1_relat_1(X60) != X58
        | ~ v1_relat_1(X60)
        | ~ v1_funct_1(X60) )
      & ( m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
        | r2_hidden(esk6_3(X58,X59,X60),X58)
        | k1_relat_1(X60) != X58
        | ~ v1_relat_1(X60)
        | ~ v1_funct_1(X60) )
      & ( v1_funct_1(X60)
        | ~ r2_hidden(k1_funct_1(X60,esk6_3(X58,X59,X60)),X59)
        | k1_relat_1(X60) != X58
        | ~ v1_relat_1(X60)
        | ~ v1_funct_1(X60) )
      & ( v1_funct_2(X60,X58,X59)
        | ~ r2_hidden(k1_funct_1(X60,esk6_3(X58,X59,X60)),X59)
        | k1_relat_1(X60) != X58
        | ~ v1_relat_1(X60)
        | ~ v1_funct_1(X60) )
      & ( m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
        | ~ r2_hidden(k1_funct_1(X60,esk6_3(X58,X59,X60)),X59)
        | k1_relat_1(X60) != X58
        | ~ v1_relat_1(X60)
        | ~ v1_funct_1(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_relset_1(X32,X33,X34) = k1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | r2_hidden(esk6_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_58,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_funct_1(esk9_0)
    | ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | r2_hidden(esk6_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( v1_funct_2(X1,X2,X3)
    | r2_hidden(esk6_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_63,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ r1_tarski(k1_relat_1(X37),X35)
      | ~ r1_tarski(k2_relat_1(X37),X36)
      | m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_64,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_45])).

fof(c_0_66,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | m1_subset_1(k1_relset_1(X29,X30,X31),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_67,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk9_0,X1)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_50])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_37])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,X1)))
    | r2_hidden(esk6_3(esk7_0,X1,esk9_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_37]),c_0_36]),c_0_36]),c_0_36]),c_0_38])])).

cnf(c_0_71,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | r2_hidden(esk6_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( r1_tarski(k2_relat_1(esk3_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_74,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)) = esk9_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_75,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( k1_relset_1(X1,X2,esk9_0) = esk7_0
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_36])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk6_3(esk7_0,esk8_0,esk9_0),esk7_0)
    | ~ v1_funct_2(esk9_0,esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,X1)
    | r2_hidden(esk6_3(esk7_0,X1,esk9_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_37]),c_0_36]),c_0_36]),c_0_36]),c_0_38])])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ v1_funct_1(esk9_0)
    | ~ v1_relat_1(esk9_0)
    | ~ r1_tarski(k1_relat_1(esk9_0),esk7_0)
    | ~ r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_72])).

cnf(c_0_80,plain,
    ( r1_tarski(k2_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_73])).

fof(c_0_81,plain,(
    ! [X41,X42,X43] :
      ( ( v1_funct_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | v1_xboole_0(X42) )
      & ( v1_partfun1(X43,X41)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | v1_xboole_0(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_82,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_83,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)) = esk9_0
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_53])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,X1)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ r1_tarski(k1_relat_1(esk9_0),esk7_0)
    | ~ r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_37])]),c_0_38])])).

cnf(c_0_88,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_22])).

fof(c_0_89,plain,(
    ! [X38,X39,X40] :
      ( ( v1_funct_1(X40)
        | ~ v1_funct_1(X40)
        | ~ v1_partfun1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v1_funct_2(X40,X38,X39)
        | ~ v1_funct_1(X40)
        | ~ v1_partfun1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_90,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk9_0))
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_83])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_40]),c_0_68])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_36]),c_0_47])])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_28])).

cnf(c_0_97,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( v1_partfun1(esk9_0,esk7_0)
    | v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_45]),c_0_91]),c_0_37])])).

cnf(c_0_99,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96])])).

cnf(c_0_101,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_97,c_0_72])).

cnf(c_0_102,negated_conjecture,
    ( v1_partfun1(esk9_0,esk7_0) ),
    inference(sr,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102]),c_0_37]),c_0_38]),c_0_36]),c_0_47]),c_0_96])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.029 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.20/0.44  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.20/0.44  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.44  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.20/0.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.44  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.44  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.44  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 0.20/0.44  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.44  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.20/0.44  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.20/0.44  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.20/0.44  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.20/0.44  fof(c_0_15, plain, ![X44, X45, X46, X47, X49, X50, X51, X52, X53, X55]:(((((((v1_relat_1(esk3_4(X44,X45,X46,X47))|~r2_hidden(X47,X46)|X46!=k1_funct_2(X44,X45))&(v1_funct_1(esk3_4(X44,X45,X46,X47))|~r2_hidden(X47,X46)|X46!=k1_funct_2(X44,X45)))&(X47=esk3_4(X44,X45,X46,X47)|~r2_hidden(X47,X46)|X46!=k1_funct_2(X44,X45)))&(k1_relat_1(esk3_4(X44,X45,X46,X47))=X44|~r2_hidden(X47,X46)|X46!=k1_funct_2(X44,X45)))&(r1_tarski(k2_relat_1(esk3_4(X44,X45,X46,X47)),X45)|~r2_hidden(X47,X46)|X46!=k1_funct_2(X44,X45)))&(~v1_relat_1(X50)|~v1_funct_1(X50)|X49!=X50|k1_relat_1(X50)!=X44|~r1_tarski(k2_relat_1(X50),X45)|r2_hidden(X49,X46)|X46!=k1_funct_2(X44,X45)))&((~r2_hidden(esk4_3(X51,X52,X53),X53)|(~v1_relat_1(X55)|~v1_funct_1(X55)|esk4_3(X51,X52,X53)!=X55|k1_relat_1(X55)!=X51|~r1_tarski(k2_relat_1(X55),X52))|X53=k1_funct_2(X51,X52))&(((((v1_relat_1(esk5_3(X51,X52,X53))|r2_hidden(esk4_3(X51,X52,X53),X53)|X53=k1_funct_2(X51,X52))&(v1_funct_1(esk5_3(X51,X52,X53))|r2_hidden(esk4_3(X51,X52,X53),X53)|X53=k1_funct_2(X51,X52)))&(esk4_3(X51,X52,X53)=esk5_3(X51,X52,X53)|r2_hidden(esk4_3(X51,X52,X53),X53)|X53=k1_funct_2(X51,X52)))&(k1_relat_1(esk5_3(X51,X52,X53))=X51|r2_hidden(esk4_3(X51,X52,X53),X53)|X53=k1_funct_2(X51,X52)))&(r1_tarski(k2_relat_1(esk5_3(X51,X52,X53)),X52)|r2_hidden(esk4_3(X51,X52,X53),X53)|X53=k1_funct_2(X51,X52))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.20/0.44  cnf(c_0_16, plain, (k1_relat_1(esk3_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.44  cnf(c_0_17, plain, (X1=esk3_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.44  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.20/0.44  cnf(c_0_19, plain, (v1_funct_1(esk3_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.44  cnf(c_0_20, plain, (v1_relat_1(esk3_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.44  cnf(c_0_21, plain, (k1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.44  cnf(c_0_22, plain, (esk3_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.44  fof(c_0_23, negated_conjecture, (r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))&(~v1_funct_1(esk9_0)|~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.20/0.44  cnf(c_0_24, plain, (v1_funct_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.20/0.44  cnf(c_0_25, plain, (v1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.20/0.44  fof(c_0_26, plain, ![X57]:(((v1_funct_1(X57)|(~v1_relat_1(X57)|~v1_funct_1(X57)))&(v1_funct_2(X57,k1_relat_1(X57),k2_relat_1(X57))|(~v1_relat_1(X57)|~v1_funct_1(X57))))&(m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X57),k2_relat_1(X57))))|(~v1_relat_1(X57)|~v1_funct_1(X57)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.44  cnf(c_0_27, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.44  cnf(c_0_28, negated_conjecture, (r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  cnf(c_0_29, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.20/0.44  cnf(c_0_30, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 0.20/0.44  fof(c_0_31, plain, ![X26, X27, X28]:(~v1_xboole_0(X26)|(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X26)))|v1_xboole_0(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.20/0.44  fof(c_0_32, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.44  fof(c_0_33, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.44  fof(c_0_34, plain, ![X23, X24, X25]:(~r2_hidden(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X25))|~v1_xboole_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.44  cnf(c_0_35, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.44  cnf(c_0_36, negated_conjecture, (k1_relat_1(esk9_0)=esk7_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.44  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk9_0)), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.20/0.44  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 0.20/0.44  cnf(c_0_39, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.44  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.44  cnf(c_0_41, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.44  fof(c_0_42, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.44  fof(c_0_43, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.44  cnf(c_0_44, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.44  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])])).
% 0.20/0.44  cnf(c_0_46, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.44  cnf(c_0_47, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_41])).
% 0.20/0.44  fof(c_0_48, plain, ![X58, X59, X60]:((((v1_funct_1(X60)|(r2_hidden(esk6_3(X58,X59,X60),X58)|k1_relat_1(X60)!=X58)|(~v1_relat_1(X60)|~v1_funct_1(X60)))&(v1_funct_2(X60,X58,X59)|(r2_hidden(esk6_3(X58,X59,X60),X58)|k1_relat_1(X60)!=X58)|(~v1_relat_1(X60)|~v1_funct_1(X60))))&(m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))|(r2_hidden(esk6_3(X58,X59,X60),X58)|k1_relat_1(X60)!=X58)|(~v1_relat_1(X60)|~v1_funct_1(X60))))&(((v1_funct_1(X60)|(~r2_hidden(k1_funct_1(X60,esk6_3(X58,X59,X60)),X59)|k1_relat_1(X60)!=X58)|(~v1_relat_1(X60)|~v1_funct_1(X60)))&(v1_funct_2(X60,X58,X59)|(~r2_hidden(k1_funct_1(X60,esk6_3(X58,X59,X60)),X59)|k1_relat_1(X60)!=X58)|(~v1_relat_1(X60)|~v1_funct_1(X60))))&(m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))|(~r2_hidden(k1_funct_1(X60,esk6_3(X58,X59,X60)),X59)|k1_relat_1(X60)!=X58)|(~v1_relat_1(X60)|~v1_funct_1(X60))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.20/0.44  cnf(c_0_49, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.44  cnf(c_0_50, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.44  fof(c_0_51, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k1_relset_1(X32,X33,X34)=k1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.44  cnf(c_0_52, negated_conjecture, (~r2_hidden(X1,esk9_0)|~v1_xboole_0(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.44  cnf(c_0_53, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.44  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|r2_hidden(esk6_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.44  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.44  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.44  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.44  cnf(c_0_58, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.44  cnf(c_0_59, negated_conjecture, (~r2_hidden(X1,esk9_0)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.44  cnf(c_0_60, negated_conjecture, (~v1_funct_1(esk9_0)|~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|r2_hidden(esk6_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_54])).
% 0.20/0.44  cnf(c_0_62, plain, (v1_funct_2(X1,X2,X3)|r2_hidden(esk6_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.44  fof(c_0_63, plain, ![X35, X36, X37]:(~v1_relat_1(X37)|(~r1_tarski(k1_relat_1(X37),X35)|~r1_tarski(k2_relat_1(X37),X36)|m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.20/0.44  cnf(c_0_64, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.44  cnf(c_0_65, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))), inference(spm,[status(thm)],[c_0_57, c_0_45])).
% 0.20/0.44  fof(c_0_66, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|m1_subset_1(k1_relset_1(X29,X30,X31),k1_zfmisc_1(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.20/0.44  cnf(c_0_67, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_58, c_0_40])).
% 0.20/0.44  cnf(c_0_68, negated_conjecture, (r1_tarski(esk9_0,X1)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_59, c_0_50])).
% 0.20/0.44  cnf(c_0_69, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_37])])).
% 0.20/0.44  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,X1)))|r2_hidden(esk6_3(esk7_0,X1,esk9_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_37]), c_0_36]), c_0_36]), c_0_36]), c_0_38])])).
% 0.20/0.44  cnf(c_0_71, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|r2_hidden(esk6_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_62])).
% 0.20/0.44  cnf(c_0_72, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.44  cnf(c_0_73, plain, (r1_tarski(k2_relat_1(esk3_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.44  cnf(c_0_74, negated_conjecture, (k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))=esk9_0|~v1_xboole_0(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.44  cnf(c_0_75, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.44  cnf(c_0_76, negated_conjecture, (k1_relset_1(X1,X2,esk9_0)=esk7_0|~v1_xboole_0(k2_relat_1(esk9_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_36])).
% 0.20/0.44  cnf(c_0_77, negated_conjecture, (r2_hidden(esk6_3(esk7_0,esk8_0,esk9_0),esk7_0)|~v1_funct_2(esk9_0,esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.44  cnf(c_0_78, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,X1)|r2_hidden(esk6_3(esk7_0,X1,esk9_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_37]), c_0_36]), c_0_36]), c_0_36]), c_0_38])])).
% 0.20/0.44  cnf(c_0_79, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~v1_funct_1(esk9_0)|~v1_relat_1(esk9_0)|~r1_tarski(k1_relat_1(esk9_0),esk7_0)|~r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_60, c_0_72])).
% 0.20/0.44  cnf(c_0_80, plain, (r1_tarski(k2_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_73])).
% 0.20/0.44  fof(c_0_81, plain, ![X41, X42, X43]:((v1_funct_1(X43)|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X42))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|v1_xboole_0(X42))&(v1_partfun1(X43,X41)|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X42))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|v1_xboole_0(X42))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.20/0.44  cnf(c_0_82, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.44  cnf(c_0_83, negated_conjecture, (k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))=esk9_0|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_74, c_0_53])).
% 0.20/0.44  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(X1))|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.44  cnf(c_0_85, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_49, c_0_77])).
% 0.20/0.44  cnf(c_0_86, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,X1)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_49, c_0_78])).
% 0.20/0.44  cnf(c_0_87, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~r1_tarski(k1_relat_1(esk9_0),esk7_0)|~r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_37])]), c_0_38])])).
% 0.20/0.44  cnf(c_0_88, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_80, c_0_22])).
% 0.20/0.44  fof(c_0_89, plain, ![X38, X39, X40]:((v1_funct_1(X40)|(~v1_funct_1(X40)|~v1_partfun1(X40,X38))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(v1_funct_2(X40,X38,X39)|(~v1_funct_1(X40)|~v1_partfun1(X40,X38))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.20/0.44  cnf(c_0_90, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.44  cnf(c_0_91, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_36]), c_0_37]), c_0_38])])).
% 0.20/0.44  cnf(c_0_92, negated_conjecture, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk9_0))|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_39, c_0_83])).
% 0.20/0.44  cnf(c_0_93, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(X1))|~v1_xboole_0(k2_relat_1(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_40]), c_0_68])).
% 0.20/0.44  cnf(c_0_94, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.20/0.44  cnf(c_0_95, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_36]), c_0_47])])).
% 0.20/0.44  cnf(c_0_96, negated_conjecture, (r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_88, c_0_28])).
% 0.20/0.44  cnf(c_0_97, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.44  cnf(c_0_98, negated_conjecture, (v1_partfun1(esk9_0,esk7_0)|v1_xboole_0(k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_45]), c_0_91]), c_0_37])])).
% 0.20/0.44  cnf(c_0_99, negated_conjecture, (~v1_xboole_0(k2_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 0.20/0.44  cnf(c_0_100, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96])])).
% 0.20/0.44  cnf(c_0_101, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_97, c_0_72])).
% 0.20/0.44  cnf(c_0_102, negated_conjecture, (v1_partfun1(esk9_0,esk7_0)), inference(sr,[status(thm)],[c_0_98, c_0_99])).
% 0.20/0.44  cnf(c_0_103, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102]), c_0_37]), c_0_38]), c_0_36]), c_0_47]), c_0_96])]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 104
% 0.20/0.44  # Proof object clause steps            : 73
% 0.20/0.44  # Proof object formula steps           : 31
% 0.20/0.44  # Proof object conjectures             : 36
% 0.20/0.44  # Proof object clause conjectures      : 33
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 24
% 0.20/0.44  # Proof object initial formulas used   : 15
% 0.20/0.44  # Proof object generating inferences   : 36
% 0.20/0.44  # Proof object simplifying inferences  : 49
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 16
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 43
% 0.20/0.44  # Removed in clause preprocessing      : 5
% 0.20/0.44  # Initial clauses in saturation        : 38
% 0.20/0.44  # Processed clauses                    : 996
% 0.20/0.44  # ...of these trivial                  : 0
% 0.20/0.44  # ...subsumed                          : 634
% 0.20/0.44  # ...remaining for further processing  : 362
% 0.20/0.44  # Other redundant clauses eliminated   : 15
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 41
% 0.20/0.44  # Backward-rewritten                   : 11
% 0.20/0.44  # Generated clauses                    : 2566
% 0.20/0.44  # ...of the previous two non-trivial   : 2441
% 0.20/0.44  # Contextual simplify-reflections      : 11
% 0.20/0.44  # Paramodulations                      : 2552
% 0.20/0.44  # Factorizations                       : 0
% 0.20/0.44  # Equation resolutions                 : 15
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 259
% 0.20/0.44  #    Positive orientable unit clauses  : 17
% 0.20/0.44  #    Positive unorientable unit clauses: 0
% 0.20/0.44  #    Negative unit clauses             : 6
% 0.20/0.44  #    Non-unit-clauses                  : 236
% 0.20/0.44  # Current number of unprocessed clauses: 1461
% 0.20/0.44  # ...number of literals in the above   : 6519
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 90
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 19369
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 9850
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 485
% 0.20/0.44  # Unit Clause-clause subsumption calls : 498
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 10
% 0.20/0.44  # BW rewrite match successes           : 4
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 35967
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.097 s
% 0.20/0.45  # System time              : 0.007 s
% 0.20/0.45  # Total time               : 0.104 s
% 0.20/0.45  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
