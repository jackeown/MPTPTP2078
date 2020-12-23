%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  139 (1043 expanded)
%              Number of clauses        :   97 ( 526 expanded)
%              Number of leaves         :   21 ( 240 expanded)
%              Depth                    :   15
%              Number of atoms          :  427 (6652 expanded)
%              Number of equality atoms :   48 (2219 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t121_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

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

fof(c_0_21,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_22,plain,(
    ! [X21] : m1_subset_1(esk3_1(X21),X21) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_23,plain,(
    ! [X25,X26,X27] :
      ( ~ r2_hidden(X25,X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X27))
      | ~ v1_xboole_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_24,plain,(
    ! [X18] :
      ( ~ r1_tarski(X18,k1_xboole_0)
      | X18 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(esk3_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X54,X55,X56,X57,X59,X60,X61,X62,X63,X65] :
      ( ( v1_relat_1(esk4_4(X54,X55,X56,X57))
        | ~ r2_hidden(X57,X56)
        | X56 != k1_funct_2(X54,X55) )
      & ( v1_funct_1(esk4_4(X54,X55,X56,X57))
        | ~ r2_hidden(X57,X56)
        | X56 != k1_funct_2(X54,X55) )
      & ( X57 = esk4_4(X54,X55,X56,X57)
        | ~ r2_hidden(X57,X56)
        | X56 != k1_funct_2(X54,X55) )
      & ( k1_relat_1(esk4_4(X54,X55,X56,X57)) = X54
        | ~ r2_hidden(X57,X56)
        | X56 != k1_funct_2(X54,X55) )
      & ( r1_tarski(k2_relat_1(esk4_4(X54,X55,X56,X57)),X55)
        | ~ r2_hidden(X57,X56)
        | X56 != k1_funct_2(X54,X55) )
      & ( ~ v1_relat_1(X60)
        | ~ v1_funct_1(X60)
        | X59 != X60
        | k1_relat_1(X60) != X54
        | ~ r1_tarski(k2_relat_1(X60),X55)
        | r2_hidden(X59,X56)
        | X56 != k1_funct_2(X54,X55) )
      & ( ~ r2_hidden(esk5_3(X61,X62,X63),X63)
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65)
        | esk5_3(X61,X62,X63) != X65
        | k1_relat_1(X65) != X61
        | ~ r1_tarski(k2_relat_1(X65),X62)
        | X63 = k1_funct_2(X61,X62) )
      & ( v1_relat_1(esk6_3(X61,X62,X63))
        | r2_hidden(esk5_3(X61,X62,X63),X63)
        | X63 = k1_funct_2(X61,X62) )
      & ( v1_funct_1(esk6_3(X61,X62,X63))
        | r2_hidden(esk5_3(X61,X62,X63),X63)
        | X63 = k1_funct_2(X61,X62) )
      & ( esk5_3(X61,X62,X63) = esk6_3(X61,X62,X63)
        | r2_hidden(esk5_3(X61,X62,X63),X63)
        | X63 = k1_funct_2(X61,X62) )
      & ( k1_relat_1(esk6_3(X61,X62,X63)) = X61
        | r2_hidden(esk5_3(X61,X62,X63),X63)
        | X63 = k1_funct_2(X61,X62) )
      & ( r1_tarski(k2_relat_1(esk6_3(X61,X62,X63)),X62)
        | r2_hidden(esk5_3(X61,X62,X63),X63)
        | X63 = k1_funct_2(X61,X62) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_31,plain,(
    ! [X35,X36,X37] :
      ( ( v4_relat_1(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( v5_relat_1(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,esk3_1(k1_zfmisc_1(X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_33,plain,
    ( esk3_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_35,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_36,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | v1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_37,plain,
    ( k1_relat_1(esk4_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( X1 = esk4_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_40,plain,
    ( v1_funct_1(esk4_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( v1_relat_1(esk4_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_45,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k1_relat_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( esk4_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_38])).

fof(c_0_49,negated_conjecture,
    ( r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))
    & ( ~ v1_funct_1(esk9_0)
      | ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
      | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_50,plain,
    ( v1_funct_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( v1_relat_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_41])).

fof(c_0_52,plain,(
    ! [X30,X31] :
      ( ( r1_tarski(k1_relat_1(X30),k1_relat_1(X31))
        | ~ r1_tarski(X30,X31)
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
      & ( r1_tarski(k2_relat_1(X30),k2_relat_1(X31))
        | ~ r1_tarski(X30,X31)
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_53,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X20,X19)
        | r2_hidden(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ r2_hidden(X20,X19)
        | m1_subset_1(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ m1_subset_1(X20,X19)
        | v1_xboole_0(X20)
        | ~ v1_xboole_0(X19) )
      & ( ~ v1_xboole_0(X20)
        | m1_subset_1(X20,X19)
        | ~ v1_xboole_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_54,plain,(
    ! [X28,X29] :
      ( ( ~ v4_relat_1(X29,X28)
        | r1_tarski(k1_relat_1(X29),X28)
        | ~ v1_relat_1(X29) )
      & ( ~ r1_tarski(k1_relat_1(X29),X28)
        | v4_relat_1(X29,X28)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_55,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_43])).

fof(c_0_58,plain,(
    ! [X67] :
      ( ( v1_funct_1(X67)
        | ~ v1_relat_1(X67)
        | ~ v1_funct_1(X67) )
      & ( v1_funct_2(X67,k1_relat_1(X67),k2_relat_1(X67))
        | ~ v1_relat_1(X67)
        | ~ v1_funct_1(X67) )
      & ( m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X67),k2_relat_1(X67))))
        | ~ v1_relat_1(X67)
        | ~ v1_funct_1(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_59,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_62,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_48])).

fof(c_0_63,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_xboole_0(X38)
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X38)))
      | v1_xboole_0(X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_64,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_65,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_43])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_69,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_70,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_60])).

fof(c_0_75,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_76,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_78,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_79,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_26])).

cnf(c_0_80,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74])])).

cnf(c_0_82,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_76,c_0_43])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_77])).

fof(c_0_85,plain,(
    ! [X41,X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X41)))
      | ~ r1_tarski(k2_relat_1(X44),X42)
      | m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X42))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

cnf(c_0_86,plain,
    ( r1_tarski(k2_relat_1(esk4_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_87,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_80])).

cnf(c_0_89,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_81])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_45])).

cnf(c_0_92,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_93,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_94,plain,
    ( r1_tarski(k2_relat_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_funct_1(esk9_0)
    | ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_96,plain,(
    ! [X45,X46,X47] :
      ( ( v1_funct_1(X47)
        | ~ v1_funct_1(X47)
        | ~ v1_partfun1(X47,X45)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( v1_funct_2(X47,X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_partfun1(X47,X45)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

fof(c_0_97,plain,(
    ! [X48,X49,X50] :
      ( ~ v1_xboole_0(X48)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | v1_partfun1(X50,X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_98,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_70]),c_0_34])])).

cnf(c_0_99,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)) = esk9_0
    | ~ r1_tarski(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_100,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_81])).

cnf(c_0_102,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_48])).

cnf(c_0_103,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_73])])).

cnf(c_0_104,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_105,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_106,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_107,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ r1_tarski(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_72]),c_0_74])])).

cnf(c_0_108,plain,
    ( v1_xboole_0(esk3_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_26])).

cnf(c_0_109,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)) = esk9_0
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_110,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ r1_tarski(esk9_0,X1)
    | ~ r2_hidden(X2,esk7_0)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_72]),c_0_74])])).

cnf(c_0_111,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_84])).

fof(c_0_112,plain,(
    ! [X51,X52,X53] :
      ( ( v1_funct_1(X53)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | v1_xboole_0(X52) )
      & ( v1_partfun1(X53,X51)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | v1_xboole_0(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_113,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,X1))
    | ~ r1_tarski(k2_relat_1(esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_101])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_60])).

cnf(c_0_116,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0)
    | ~ r1_tarski(k2_relat_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_101])).

cnf(c_0_117,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,X1)
    | ~ v1_partfun1(esk9_0,esk7_0)
    | ~ r1_tarski(k2_relat_1(esk9_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_101]),c_0_73])])).

cnf(c_0_118,negated_conjecture,
    ( v1_partfun1(esk9_0,esk7_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_81])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(X1,esk7_0)
    | ~ r1_tarski(esk9_0,k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_120,negated_conjecture,
    ( v1_xboole_0(esk3_1(k1_zfmisc_1(esk9_0)))
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(esk9_0,X1)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_109])).

cnf(c_0_122,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ v1_xboole_0(k1_relat_1(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_90]),c_0_111])])).

cnf(c_0_123,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_100])).

cnf(c_0_124,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_125,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_72]),c_0_73]),c_0_74])])).

cnf(c_0_126,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_43])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_128,negated_conjecture,
    ( ~ v1_funct_2(esk9_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_115])])).

cnf(c_0_129,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,X1)
    | ~ r1_tarski(k2_relat_1(esk9_0),X1)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_130,negated_conjecture,
    ( m1_subset_1(esk3_1(k1_zfmisc_1(esk9_0)),esk7_0)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_121])).

cnf(c_0_131,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_88]),c_0_34])])).

cnf(c_0_132,negated_conjecture,
    ( v1_partfun1(esk9_0,esk7_0)
    | v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_81]),c_0_125]),c_0_73])])).

cnf(c_0_133,negated_conjecture,
    ( ~ v1_partfun1(esk9_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_73])]),c_0_128])).

cnf(c_0_134,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk9_0),esk8_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_129])).

cnf(c_0_135,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_130]),c_0_131])).

cnf(c_0_136,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_115])])).

cnf(c_0_138,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_136])]),c_0_137]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:34 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.50  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.030 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.50  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.20/0.50  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.50  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.50  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 0.20/0.50  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.50  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.50  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.50  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 0.20/0.50  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.20/0.50  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.50  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.50  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.50  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.20/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.50  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.50  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 0.20/0.50  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.20/0.50  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.20/0.50  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.20/0.50  fof(c_0_21, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.50  fof(c_0_22, plain, ![X21]:m1_subset_1(esk3_1(X21),X21), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.20/0.50  fof(c_0_23, plain, ![X25, X26, X27]:(~r2_hidden(X25,X26)|~m1_subset_1(X26,k1_zfmisc_1(X27))|~v1_xboole_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.50  fof(c_0_24, plain, ![X18]:(~r1_tarski(X18,k1_xboole_0)|X18=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.50  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.50  cnf(c_0_26, plain, (m1_subset_1(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.50  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.50  cnf(c_0_28, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.50  cnf(c_0_29, plain, (r1_tarski(esk3_1(k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.50  fof(c_0_30, plain, ![X54, X55, X56, X57, X59, X60, X61, X62, X63, X65]:(((((((v1_relat_1(esk4_4(X54,X55,X56,X57))|~r2_hidden(X57,X56)|X56!=k1_funct_2(X54,X55))&(v1_funct_1(esk4_4(X54,X55,X56,X57))|~r2_hidden(X57,X56)|X56!=k1_funct_2(X54,X55)))&(X57=esk4_4(X54,X55,X56,X57)|~r2_hidden(X57,X56)|X56!=k1_funct_2(X54,X55)))&(k1_relat_1(esk4_4(X54,X55,X56,X57))=X54|~r2_hidden(X57,X56)|X56!=k1_funct_2(X54,X55)))&(r1_tarski(k2_relat_1(esk4_4(X54,X55,X56,X57)),X55)|~r2_hidden(X57,X56)|X56!=k1_funct_2(X54,X55)))&(~v1_relat_1(X60)|~v1_funct_1(X60)|X59!=X60|k1_relat_1(X60)!=X54|~r1_tarski(k2_relat_1(X60),X55)|r2_hidden(X59,X56)|X56!=k1_funct_2(X54,X55)))&((~r2_hidden(esk5_3(X61,X62,X63),X63)|(~v1_relat_1(X65)|~v1_funct_1(X65)|esk5_3(X61,X62,X63)!=X65|k1_relat_1(X65)!=X61|~r1_tarski(k2_relat_1(X65),X62))|X63=k1_funct_2(X61,X62))&(((((v1_relat_1(esk6_3(X61,X62,X63))|r2_hidden(esk5_3(X61,X62,X63),X63)|X63=k1_funct_2(X61,X62))&(v1_funct_1(esk6_3(X61,X62,X63))|r2_hidden(esk5_3(X61,X62,X63),X63)|X63=k1_funct_2(X61,X62)))&(esk5_3(X61,X62,X63)=esk6_3(X61,X62,X63)|r2_hidden(esk5_3(X61,X62,X63),X63)|X63=k1_funct_2(X61,X62)))&(k1_relat_1(esk6_3(X61,X62,X63))=X61|r2_hidden(esk5_3(X61,X62,X63),X63)|X63=k1_funct_2(X61,X62)))&(r1_tarski(k2_relat_1(esk6_3(X61,X62,X63)),X62)|r2_hidden(esk5_3(X61,X62,X63),X63)|X63=k1_funct_2(X61,X62))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.20/0.50  fof(c_0_31, plain, ![X35, X36, X37]:((v4_relat_1(X37,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(v5_relat_1(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.50  cnf(c_0_32, plain, (~r2_hidden(X1,esk3_1(k1_zfmisc_1(X2)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.20/0.50  cnf(c_0_33, plain, (esk3_1(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.50  cnf(c_0_34, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.50  fof(c_0_35, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.50  fof(c_0_36, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|v1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.50  cnf(c_0_37, plain, (k1_relat_1(esk4_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.50  cnf(c_0_38, plain, (X1=esk4_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.50  fof(c_0_39, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.20/0.50  cnf(c_0_40, plain, (v1_funct_1(esk4_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.50  cnf(c_0_41, plain, (v1_relat_1(esk4_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.50  cnf(c_0_42, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.50  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.50  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.20/0.50  cnf(c_0_45, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.50  cnf(c_0_46, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.50  cnf(c_0_47, plain, (k1_relat_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_37])).
% 0.20/0.50  cnf(c_0_48, plain, (esk4_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_38])).
% 0.20/0.50  fof(c_0_49, negated_conjecture, (r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))&(~v1_funct_1(esk9_0)|~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.20/0.50  cnf(c_0_50, plain, (v1_funct_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_40])).
% 0.20/0.50  cnf(c_0_51, plain, (v1_relat_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_41])).
% 0.20/0.50  fof(c_0_52, plain, ![X30, X31]:((r1_tarski(k1_relat_1(X30),k1_relat_1(X31))|~r1_tarski(X30,X31)|~v1_relat_1(X31)|~v1_relat_1(X30))&(r1_tarski(k2_relat_1(X30),k2_relat_1(X31))|~r1_tarski(X30,X31)|~v1_relat_1(X31)|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.20/0.50  fof(c_0_53, plain, ![X19, X20]:(((~m1_subset_1(X20,X19)|r2_hidden(X20,X19)|v1_xboole_0(X19))&(~r2_hidden(X20,X19)|m1_subset_1(X20,X19)|v1_xboole_0(X19)))&((~m1_subset_1(X20,X19)|v1_xboole_0(X20)|~v1_xboole_0(X19))&(~v1_xboole_0(X20)|m1_subset_1(X20,X19)|~v1_xboole_0(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.50  fof(c_0_54, plain, ![X28, X29]:((~v4_relat_1(X29,X28)|r1_tarski(k1_relat_1(X29),X28)|~v1_relat_1(X29))&(~r1_tarski(k1_relat_1(X29),X28)|v4_relat_1(X29,X28)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.50  cnf(c_0_55, plain, (v4_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.50  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.50  cnf(c_0_57, plain, (v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_46, c_0_43])).
% 0.20/0.50  fof(c_0_58, plain, ![X67]:(((v1_funct_1(X67)|(~v1_relat_1(X67)|~v1_funct_1(X67)))&(v1_funct_2(X67,k1_relat_1(X67),k2_relat_1(X67))|(~v1_relat_1(X67)|~v1_funct_1(X67))))&(m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X67),k2_relat_1(X67))))|(~v1_relat_1(X67)|~v1_funct_1(X67)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.50  cnf(c_0_59, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.50  cnf(c_0_60, negated_conjecture, (r2_hidden(esk9_0,k1_funct_2(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.50  cnf(c_0_61, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_50, c_0_48])).
% 0.20/0.50  cnf(c_0_62, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_51, c_0_48])).
% 0.20/0.50  fof(c_0_63, plain, ![X38, X39, X40]:(~v1_xboole_0(X38)|(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X38)))|v1_xboole_0(X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.20/0.50  fof(c_0_64, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.50  cnf(c_0_65, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_27, c_0_43])).
% 0.20/0.50  cnf(c_0_66, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.50  cnf(c_0_67, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.50  cnf(c_0_68, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.50  cnf(c_0_69, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.50  cnf(c_0_70, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_56])).
% 0.20/0.50  cnf(c_0_71, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.50  cnf(c_0_72, negated_conjecture, (k1_relat_1(esk9_0)=esk7_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.50  cnf(c_0_73, negated_conjecture, (v1_funct_1(esk9_0)), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 0.20/0.50  cnf(c_0_74, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_62, c_0_60])).
% 0.20/0.50  fof(c_0_75, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.50  cnf(c_0_76, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.50  cnf(c_0_77, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.50  cnf(c_0_78, plain, (~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X2,X1)|~r2_hidden(X3,k1_relat_1(X2))|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.50  cnf(c_0_79, plain, (r2_hidden(esk3_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_67, c_0_26])).
% 0.20/0.50  cnf(c_0_80, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])).
% 0.20/0.50  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74])])).
% 0.20/0.50  cnf(c_0_82, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.50  cnf(c_0_83, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_76, c_0_43])).
% 0.20/0.50  cnf(c_0_84, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_77])).
% 0.20/0.50  fof(c_0_85, plain, ![X41, X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X41)))|(~r1_tarski(k2_relat_1(X44),X42)|m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X42))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 0.20/0.50  cnf(c_0_86, plain, (r1_tarski(k2_relat_1(esk4_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.50  cnf(c_0_87, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)|~v1_xboole_0(k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.50  cnf(c_0_88, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_80])).
% 0.20/0.50  cnf(c_0_89, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.50  cnf(c_0_90, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)))), inference(spm,[status(thm)],[c_0_25, c_0_81])).
% 0.20/0.50  cnf(c_0_91, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_82, c_0_45])).
% 0.20/0.50  cnf(c_0_92, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.50  cnf(c_0_93, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.20/0.50  cnf(c_0_94, plain, (r1_tarski(k2_relat_1(esk4_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_86])).
% 0.20/0.50  cnf(c_0_95, negated_conjecture, (~v1_funct_1(esk9_0)|~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.50  fof(c_0_96, plain, ![X45, X46, X47]:((v1_funct_1(X47)|(~v1_funct_1(X47)|~v1_partfun1(X47,X45))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(v1_funct_2(X47,X45,X46)|(~v1_funct_1(X47)|~v1_partfun1(X47,X45))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.20/0.50  fof(c_0_97, plain, ![X48, X49, X50]:(~v1_xboole_0(X48)|(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|v1_partfun1(X50,X48))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.20/0.50  cnf(c_0_98, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_70]), c_0_34])])).
% 0.20/0.50  cnf(c_0_99, negated_conjecture, (k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))=esk9_0|~r1_tarski(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0)),esk9_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.50  cnf(c_0_100, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.50  cnf(c_0_101, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,X1)))|~r1_tarski(k2_relat_1(esk9_0),X1)), inference(spm,[status(thm)],[c_0_93, c_0_81])).
% 0.20/0.50  cnf(c_0_102, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_94, c_0_48])).
% 0.20/0.50  cnf(c_0_103, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_73])])).
% 0.20/0.50  cnf(c_0_104, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.20/0.50  cnf(c_0_105, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.20/0.50  cnf(c_0_106, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.50  cnf(c_0_107, negated_conjecture, (v1_xboole_0(esk7_0)|~r1_tarski(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_72]), c_0_74])])).
% 0.20/0.50  cnf(c_0_108, plain, (v1_xboole_0(esk3_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_76, c_0_26])).
% 0.20/0.50  cnf(c_0_109, negated_conjecture, (k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))=esk9_0|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.20/0.50  cnf(c_0_110, negated_conjecture, (~v1_relat_1(X1)|~r1_tarski(esk9_0,X1)|~r2_hidden(X2,esk7_0)|~v1_xboole_0(k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_72]), c_0_74])])).
% 0.20/0.50  cnf(c_0_111, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_57, c_0_84])).
% 0.20/0.50  fof(c_0_112, plain, ![X51, X52, X53]:((v1_funct_1(X53)|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X52))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|v1_xboole_0(X52))&(v1_partfun1(X53,X51)|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X52))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|v1_xboole_0(X52))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.20/0.50  cnf(c_0_113, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.50  cnf(c_0_114, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,X1))|~r1_tarski(k2_relat_1(esk9_0),X1)), inference(spm,[status(thm)],[c_0_25, c_0_101])).
% 0.20/0.50  cnf(c_0_115, negated_conjecture, (r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_102, c_0_60])).
% 0.20/0.50  cnf(c_0_116, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)|~r1_tarski(k2_relat_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_103, c_0_101])).
% 0.20/0.50  cnf(c_0_117, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,X1)|~v1_partfun1(esk9_0,esk7_0)|~r1_tarski(k2_relat_1(esk9_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_101]), c_0_73])])).
% 0.20/0.50  cnf(c_0_118, negated_conjecture, (v1_partfun1(esk9_0,esk7_0)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_105, c_0_81])).
% 0.20/0.50  cnf(c_0_119, negated_conjecture, (m1_subset_1(X1,esk7_0)|~r1_tarski(esk9_0,k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.20/0.50  cnf(c_0_120, negated_conjecture, (v1_xboole_0(esk3_1(k1_zfmisc_1(esk9_0)))|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.20/0.50  cnf(c_0_121, negated_conjecture, (r1_tarski(esk9_0,X1)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_100, c_0_109])).
% 0.20/0.50  cnf(c_0_122, negated_conjecture, (~r2_hidden(X1,esk7_0)|~v1_xboole_0(k1_relat_1(k2_zfmisc_1(esk7_0,k2_relat_1(esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_90]), c_0_111])])).
% 0.20/0.50  cnf(c_0_123, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_28, c_0_100])).
% 0.20/0.50  cnf(c_0_124, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_112])).
% 0.20/0.50  cnf(c_0_125, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_72]), c_0_73]), c_0_74])])).
% 0.20/0.50  cnf(c_0_126, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_104, c_0_43])).
% 0.20/0.50  cnf(c_0_127, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 0.20/0.50  cnf(c_0_128, negated_conjecture, (~v1_funct_2(esk9_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_115])])).
% 0.20/0.50  cnf(c_0_129, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,X1)|~r1_tarski(k2_relat_1(esk9_0),X1)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 0.20/0.50  cnf(c_0_130, negated_conjecture, (m1_subset_1(esk3_1(k1_zfmisc_1(esk9_0)),esk7_0)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_121])).
% 0.20/0.50  cnf(c_0_131, negated_conjecture, (~r2_hidden(X1,esk7_0)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_88]), c_0_34])])).
% 0.20/0.50  cnf(c_0_132, negated_conjecture, (v1_partfun1(esk9_0,esk7_0)|v1_xboole_0(k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_81]), c_0_125]), c_0_73])])).
% 0.20/0.50  cnf(c_0_133, negated_conjecture, (~v1_partfun1(esk9_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_73])]), c_0_128])).
% 0.20/0.50  cnf(c_0_134, negated_conjecture, (~r1_tarski(k2_relat_1(esk9_0),esk8_0)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_116, c_0_129])).
% 0.20/0.50  cnf(c_0_135, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(k2_relat_1(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_130]), c_0_131])).
% 0.20/0.50  cnf(c_0_136, negated_conjecture, (v1_xboole_0(k2_relat_1(esk9_0))), inference(sr,[status(thm)],[c_0_132, c_0_133])).
% 0.20/0.50  cnf(c_0_137, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_115])])).
% 0.20/0.50  cnf(c_0_138, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_136])]), c_0_137]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 139
% 0.20/0.50  # Proof object clause steps            : 97
% 0.20/0.50  # Proof object formula steps           : 42
% 0.20/0.50  # Proof object conjectures             : 38
% 0.20/0.50  # Proof object clause conjectures      : 35
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 30
% 0.20/0.50  # Proof object initial formulas used   : 21
% 0.20/0.50  # Proof object generating inferences   : 56
% 0.20/0.50  # Proof object simplifying inferences  : 48
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 21
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 49
% 0.20/0.50  # Removed in clause preprocessing      : 3
% 0.20/0.50  # Initial clauses in saturation        : 46
% 0.20/0.50  # Processed clauses                    : 1821
% 0.20/0.50  # ...of these trivial                  : 1
% 0.20/0.50  # ...subsumed                          : 1093
% 0.20/0.50  # ...remaining for further processing  : 727
% 0.20/0.50  # Other redundant clauses eliminated   : 11
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 40
% 0.20/0.50  # Backward-rewritten                   : 112
% 0.20/0.50  # Generated clauses                    : 6016
% 0.20/0.50  # ...of the previous two non-trivial   : 5254
% 0.20/0.50  # Contextual simplify-reflections      : 36
% 0.20/0.50  # Paramodulations                      : 6006
% 0.20/0.50  # Factorizations                       : 0
% 0.20/0.50  # Equation resolutions                 : 11
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 520
% 0.20/0.50  #    Positive orientable unit clauses  : 39
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 8
% 0.20/0.50  #    Non-unit-clauses                  : 473
% 0.20/0.50  # Current number of unprocessed clauses: 3426
% 0.20/0.50  # ...number of literals in the above   : 12604
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 198
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 44699
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 31003
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 1067
% 0.20/0.50  # Unit Clause-clause subsumption calls : 1300
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 16
% 0.20/0.50  # BW rewrite match successes           : 13
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 80639
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.156 s
% 0.20/0.50  # System time              : 0.007 s
% 0.20/0.50  # Total time               : 0.163 s
% 0.20/0.50  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
