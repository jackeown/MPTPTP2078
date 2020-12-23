%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:45 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 497 expanded)
%              Number of clauses        :   53 ( 253 expanded)
%              Number of leaves         :   12 ( 107 expanded)
%              Depth                    :   13
%              Number of atoms          :  312 (3985 expanded)
%              Number of equality atoms :   53 (1476 expanded)
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

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

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

fof(c_0_12,plain,(
    ! [X41,X42,X43,X44,X46,X47,X48,X49,X50,X52] :
      ( ( v1_relat_1(esk6_4(X41,X42,X43,X44))
        | ~ r2_hidden(X44,X43)
        | X43 != k1_funct_2(X41,X42) )
      & ( v1_funct_1(esk6_4(X41,X42,X43,X44))
        | ~ r2_hidden(X44,X43)
        | X43 != k1_funct_2(X41,X42) )
      & ( X44 = esk6_4(X41,X42,X43,X44)
        | ~ r2_hidden(X44,X43)
        | X43 != k1_funct_2(X41,X42) )
      & ( k1_relat_1(esk6_4(X41,X42,X43,X44)) = X41
        | ~ r2_hidden(X44,X43)
        | X43 != k1_funct_2(X41,X42) )
      & ( r1_tarski(k2_relat_1(esk6_4(X41,X42,X43,X44)),X42)
        | ~ r2_hidden(X44,X43)
        | X43 != k1_funct_2(X41,X42) )
      & ( ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47)
        | X46 != X47
        | k1_relat_1(X47) != X41
        | ~ r1_tarski(k2_relat_1(X47),X42)
        | r2_hidden(X46,X43)
        | X43 != k1_funct_2(X41,X42) )
      & ( ~ r2_hidden(esk7_3(X48,X49,X50),X50)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52)
        | esk7_3(X48,X49,X50) != X52
        | k1_relat_1(X52) != X48
        | ~ r1_tarski(k2_relat_1(X52),X49)
        | X50 = k1_funct_2(X48,X49) )
      & ( v1_relat_1(esk8_3(X48,X49,X50))
        | r2_hidden(esk7_3(X48,X49,X50),X50)
        | X50 = k1_funct_2(X48,X49) )
      & ( v1_funct_1(esk8_3(X48,X49,X50))
        | r2_hidden(esk7_3(X48,X49,X50),X50)
        | X50 = k1_funct_2(X48,X49) )
      & ( esk7_3(X48,X49,X50) = esk8_3(X48,X49,X50)
        | r2_hidden(esk7_3(X48,X49,X50),X50)
        | X50 = k1_funct_2(X48,X49) )
      & ( k1_relat_1(esk8_3(X48,X49,X50)) = X48
        | r2_hidden(esk7_3(X48,X49,X50),X50)
        | X50 = k1_funct_2(X48,X49) )
      & ( r1_tarski(k2_relat_1(esk8_3(X48,X49,X50)),X49)
        | r2_hidden(esk7_3(X48,X49,X50),X50)
        | X50 = k1_funct_2(X48,X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_13,plain,
    ( v1_funct_1(esk6_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_14,plain,
    ( X1 = esk6_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_16,plain,
    ( v1_funct_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( esk6_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,
    ( r2_hidden(esk11_0,k1_funct_2(esk9_0,esk10_0))
    & ( ~ v1_funct_1(esk11_0)
      | ~ v1_funct_2(esk11_0,esk9_0,esk10_0)
      | ~ m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_19,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk11_0,k1_funct_2(esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( v1_relat_1(esk6_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_funct_1(esk11_0)
    | ~ v1_funct_2(esk11_0,esk9_0,esk10_0)
    | ~ m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ r1_tarski(k1_relat_1(X31),X29)
      | ~ r1_tarski(k2_relat_1(X31),X30)
      | m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_25,plain,
    ( v1_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k1_relat_1(esk6_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_funct_2(esk11_0,esk9_0,esk10_0)
    | ~ m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_30,plain,
    ( k1_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_relat_1(esk6_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_33,plain,(
    ! [X19,X20,X21,X23,X24,X25,X27] :
      ( ( r2_hidden(esk3_3(X19,X20,X21),k1_relat_1(X19))
        | ~ r2_hidden(X21,X20)
        | X20 != k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( X21 = k1_funct_1(X19,esk3_3(X19,X20,X21))
        | ~ r2_hidden(X21,X20)
        | X20 != k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(X24,k1_relat_1(X19))
        | X23 != k1_funct_1(X19,X24)
        | r2_hidden(X23,X20)
        | X20 != k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(esk4_2(X19,X25),X25)
        | ~ r2_hidden(X27,k1_relat_1(X19))
        | esk4_2(X19,X25) != k1_funct_1(X19,X27)
        | X25 = k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(esk5_2(X19,X25),k1_relat_1(X19))
        | r2_hidden(esk4_2(X19,X25),X25)
        | X25 = k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( esk4_2(X19,X25) = k1_funct_1(X19,esk5_2(X19,X25))
        | r2_hidden(esk4_2(X19,X25),X25)
        | X25 = k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_funct_2(esk11_0,esk9_0,esk10_0)
    | ~ v1_relat_1(esk11_0)
    | ~ r1_tarski(k1_relat_1(esk11_0),esk9_0)
    | ~ r1_tarski(k2_relat_1(esk11_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_36,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_17])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_xboole_0(X35)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | v1_partfun1(X37,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

fof(c_0_40,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_42,plain,(
    ! [X54] :
      ( ( v1_funct_1(X54)
        | ~ v1_relat_1(X54)
        | ~ v1_funct_1(X54) )
      & ( v1_funct_2(X54,k1_relat_1(X54),k2_relat_1(X54))
        | ~ v1_relat_1(X54)
        | ~ v1_funct_1(X54) )
      & ( m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X54),k2_relat_1(X54))))
        | ~ v1_relat_1(X54)
        | ~ v1_funct_1(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_funct_2(esk11_0,esk9_0,esk10_0)
    | ~ r1_tarski(k1_relat_1(esk11_0),esk9_0)
    | ~ r1_tarski(k2_relat_1(esk11_0),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk11_0) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_17])).

fof(c_0_47,plain,(
    ! [X32,X33,X34] :
      ( ( v1_funct_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v1_partfun1(X34,X32)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v1_funct_2(X34,X32,X33)
        | ~ v1_funct_1(X34)
        | ~ v1_partfun1(X34,X32)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_48,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).

fof(c_0_51,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,X15)
      | v1_xboole_0(X15)
      | r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_52,plain,(
    ! [X12] : m1_subset_1(esk2_1(X12),X12) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_53,plain,(
    ! [X38,X39,X40] :
      ( ( v1_funct_1(X40)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | v1_xboole_0(X39) )
      & ( v1_partfun1(X40,X38)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | v1_xboole_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_funct_2(esk11_0,esk9_0,esk10_0)
    | ~ r1_tarski(k2_relat_1(esk11_0),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk11_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_20])).

cnf(c_0_58,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_28])).

cnf(c_0_60,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( m1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,k2_relat_1(esk11_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_44]),c_0_23]),c_0_35])])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(esk11_0,esk9_0,k2_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_44]),c_0_23]),c_0_35])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_funct_2(esk11_0,esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_67,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_58,c_0_28])).

cnf(c_0_68,negated_conjecture,
    ( v1_partfun1(esk11_0,X1)
    | ~ r1_tarski(k2_relat_1(esk11_0),X2)
    | ~ r1_tarski(esk9_0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_44]),c_0_35])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ v1_xboole_0(k2_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_44]),c_0_23]),c_0_35])])).

cnf(c_0_70,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( v1_partfun1(esk11_0,esk9_0)
    | v1_xboole_0(k2_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_23])])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_partfun1(esk11_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_23]),c_0_35]),c_0_44]),c_0_45]),c_0_57])])).

cnf(c_0_73,negated_conjecture,
    ( v1_partfun1(esk11_0,X1)
    | ~ r1_tarski(esk9_0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_45])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | ~ v1_xboole_0(k2_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk11_0)) ),
    inference(sr,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_45])])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])]),c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.029 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.21/0.40  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.21/0.40  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.21/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.40  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.21/0.40  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.21/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.40  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.21/0.40  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.21/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.21/0.40  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.21/0.40  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.21/0.40  fof(c_0_12, plain, ![X41, X42, X43, X44, X46, X47, X48, X49, X50, X52]:(((((((v1_relat_1(esk6_4(X41,X42,X43,X44))|~r2_hidden(X44,X43)|X43!=k1_funct_2(X41,X42))&(v1_funct_1(esk6_4(X41,X42,X43,X44))|~r2_hidden(X44,X43)|X43!=k1_funct_2(X41,X42)))&(X44=esk6_4(X41,X42,X43,X44)|~r2_hidden(X44,X43)|X43!=k1_funct_2(X41,X42)))&(k1_relat_1(esk6_4(X41,X42,X43,X44))=X41|~r2_hidden(X44,X43)|X43!=k1_funct_2(X41,X42)))&(r1_tarski(k2_relat_1(esk6_4(X41,X42,X43,X44)),X42)|~r2_hidden(X44,X43)|X43!=k1_funct_2(X41,X42)))&(~v1_relat_1(X47)|~v1_funct_1(X47)|X46!=X47|k1_relat_1(X47)!=X41|~r1_tarski(k2_relat_1(X47),X42)|r2_hidden(X46,X43)|X43!=k1_funct_2(X41,X42)))&((~r2_hidden(esk7_3(X48,X49,X50),X50)|(~v1_relat_1(X52)|~v1_funct_1(X52)|esk7_3(X48,X49,X50)!=X52|k1_relat_1(X52)!=X48|~r1_tarski(k2_relat_1(X52),X49))|X50=k1_funct_2(X48,X49))&(((((v1_relat_1(esk8_3(X48,X49,X50))|r2_hidden(esk7_3(X48,X49,X50),X50)|X50=k1_funct_2(X48,X49))&(v1_funct_1(esk8_3(X48,X49,X50))|r2_hidden(esk7_3(X48,X49,X50),X50)|X50=k1_funct_2(X48,X49)))&(esk7_3(X48,X49,X50)=esk8_3(X48,X49,X50)|r2_hidden(esk7_3(X48,X49,X50),X50)|X50=k1_funct_2(X48,X49)))&(k1_relat_1(esk8_3(X48,X49,X50))=X48|r2_hidden(esk7_3(X48,X49,X50),X50)|X50=k1_funct_2(X48,X49)))&(r1_tarski(k2_relat_1(esk8_3(X48,X49,X50)),X49)|r2_hidden(esk7_3(X48,X49,X50),X50)|X50=k1_funct_2(X48,X49))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.21/0.40  cnf(c_0_13, plain, (v1_funct_1(esk6_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_14, plain, (X1=esk6_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.21/0.40  cnf(c_0_16, plain, (v1_funct_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_17, plain, (esk6_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_14])).
% 0.21/0.40  fof(c_0_18, negated_conjecture, (r2_hidden(esk11_0,k1_funct_2(esk9_0,esk10_0))&(~v1_funct_1(esk11_0)|~v1_funct_2(esk11_0,esk9_0,esk10_0)|~m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.21/0.40  cnf(c_0_19, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.40  cnf(c_0_20, negated_conjecture, (r2_hidden(esk11_0,k1_funct_2(esk9_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.40  cnf(c_0_21, plain, (v1_relat_1(esk6_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_22, negated_conjecture, (~v1_funct_1(esk11_0)|~v1_funct_2(esk11_0,esk9_0,esk10_0)|~m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.40  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk11_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.40  fof(c_0_24, plain, ![X29, X30, X31]:(~v1_relat_1(X31)|(~r1_tarski(k1_relat_1(X31),X29)|~r1_tarski(k2_relat_1(X31),X30)|m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.21/0.40  cnf(c_0_25, plain, (v1_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_21])).
% 0.21/0.40  cnf(c_0_26, plain, (k1_relat_1(esk6_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_27, negated_conjecture, (~v1_funct_2(esk11_0,esk9_0,esk10_0)|~m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])])).
% 0.21/0.40  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.40  cnf(c_0_29, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_25, c_0_17])).
% 0.21/0.40  cnf(c_0_30, plain, (k1_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_26])).
% 0.21/0.40  fof(c_0_31, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.40  cnf(c_0_32, plain, (r1_tarski(k2_relat_1(esk6_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  fof(c_0_33, plain, ![X19, X20, X21, X23, X24, X25, X27]:((((r2_hidden(esk3_3(X19,X20,X21),k1_relat_1(X19))|~r2_hidden(X21,X20)|X20!=k2_relat_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(X21=k1_funct_1(X19,esk3_3(X19,X20,X21))|~r2_hidden(X21,X20)|X20!=k2_relat_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19))))&(~r2_hidden(X24,k1_relat_1(X19))|X23!=k1_funct_1(X19,X24)|r2_hidden(X23,X20)|X20!=k2_relat_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19))))&((~r2_hidden(esk4_2(X19,X25),X25)|(~r2_hidden(X27,k1_relat_1(X19))|esk4_2(X19,X25)!=k1_funct_1(X19,X27))|X25=k2_relat_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&((r2_hidden(esk5_2(X19,X25),k1_relat_1(X19))|r2_hidden(esk4_2(X19,X25),X25)|X25=k2_relat_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(esk4_2(X19,X25)=k1_funct_1(X19,esk5_2(X19,X25))|r2_hidden(esk4_2(X19,X25),X25)|X25=k2_relat_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.21/0.40  cnf(c_0_34, negated_conjecture, (~v1_funct_2(esk11_0,esk9_0,esk10_0)|~v1_relat_1(esk11_0)|~r1_tarski(k1_relat_1(esk11_0),esk9_0)|~r1_tarski(k2_relat_1(esk11_0),esk10_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.40  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_29, c_0_20])).
% 0.21/0.40  cnf(c_0_36, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_30, c_0_17])).
% 0.21/0.40  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.40  cnf(c_0_38, plain, (r1_tarski(k2_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_32])).
% 0.21/0.40  fof(c_0_39, plain, ![X35, X36, X37]:(~v1_xboole_0(X35)|(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|v1_partfun1(X37,X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.21/0.40  fof(c_0_40, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.40  cnf(c_0_41, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.40  fof(c_0_42, plain, ![X54]:(((v1_funct_1(X54)|(~v1_relat_1(X54)|~v1_funct_1(X54)))&(v1_funct_2(X54,k1_relat_1(X54),k2_relat_1(X54))|(~v1_relat_1(X54)|~v1_funct_1(X54))))&(m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X54),k2_relat_1(X54))))|(~v1_relat_1(X54)|~v1_funct_1(X54)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.21/0.40  cnf(c_0_43, negated_conjecture, (~v1_funct_2(esk11_0,esk9_0,esk10_0)|~r1_tarski(k1_relat_1(esk11_0),esk9_0)|~r1_tarski(k2_relat_1(esk11_0),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.21/0.40  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk11_0)=esk9_0), inference(spm,[status(thm)],[c_0_36, c_0_20])).
% 0.21/0.40  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37])).
% 0.21/0.40  cnf(c_0_46, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_38, c_0_17])).
% 0.21/0.40  fof(c_0_47, plain, ![X32, X33, X34]:((v1_funct_1(X34)|(~v1_funct_1(X34)|~v1_partfun1(X34,X32))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(v1_funct_2(X34,X32,X33)|(~v1_funct_1(X34)|~v1_partfun1(X34,X32))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.21/0.40  cnf(c_0_48, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.40  cnf(c_0_49, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.40  cnf(c_0_50, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).
% 0.21/0.40  fof(c_0_51, plain, ![X14, X15]:(~m1_subset_1(X14,X15)|(v1_xboole_0(X15)|r2_hidden(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.21/0.40  fof(c_0_52, plain, ![X12]:m1_subset_1(esk2_1(X12),X12), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.21/0.40  fof(c_0_53, plain, ![X38, X39, X40]:((v1_funct_1(X40)|(~v1_funct_1(X40)|~v1_funct_2(X40,X38,X39))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|v1_xboole_0(X39))&(v1_partfun1(X40,X38)|(~v1_funct_1(X40)|~v1_funct_2(X40,X38,X39))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|v1_xboole_0(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.21/0.40  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.40  cnf(c_0_55, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.40  cnf(c_0_56, negated_conjecture, (~v1_funct_2(esk11_0,esk9_0,esk10_0)|~r1_tarski(k2_relat_1(esk11_0),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.21/0.40  cnf(c_0_57, negated_conjecture, (r1_tarski(k2_relat_1(esk11_0),esk10_0)), inference(spm,[status(thm)],[c_0_46, c_0_20])).
% 0.21/0.40  cnf(c_0_58, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.40  cnf(c_0_59, plain, (v1_partfun1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_48, c_0_28])).
% 0.21/0.40  cnf(c_0_60, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.40  cnf(c_0_61, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.40  cnf(c_0_62, plain, (m1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.40  cnf(c_0_63, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.40  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,k2_relat_1(esk11_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_44]), c_0_23]), c_0_35])])).
% 0.21/0.40  cnf(c_0_65, negated_conjecture, (v1_funct_2(esk11_0,esk9_0,k2_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_44]), c_0_23]), c_0_35])])).
% 0.21/0.40  cnf(c_0_66, negated_conjecture, (~v1_funct_2(esk11_0,esk9_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.21/0.40  cnf(c_0_67, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_58, c_0_28])).
% 0.21/0.40  cnf(c_0_68, negated_conjecture, (v1_partfun1(esk11_0,X1)|~r1_tarski(k2_relat_1(esk11_0),X2)|~r1_tarski(esk9_0,X1)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_44]), c_0_35])])).
% 0.21/0.40  cnf(c_0_69, negated_conjecture, (~r2_hidden(X1,esk9_0)|~v1_xboole_0(k2_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_44]), c_0_23]), c_0_35])])).
% 0.21/0.40  cnf(c_0_70, plain, (r2_hidden(esk2_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.21/0.40  cnf(c_0_71, negated_conjecture, (v1_partfun1(esk11_0,esk9_0)|v1_xboole_0(k2_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_23])])).
% 0.21/0.40  cnf(c_0_72, negated_conjecture, (~v1_partfun1(esk11_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_23]), c_0_35]), c_0_44]), c_0_45]), c_0_57])])).
% 0.21/0.40  cnf(c_0_73, negated_conjecture, (v1_partfun1(esk11_0,X1)|~r1_tarski(esk9_0,X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_45])).
% 0.21/0.40  cnf(c_0_74, negated_conjecture, (v1_xboole_0(esk9_0)|~v1_xboole_0(k2_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.21/0.40  cnf(c_0_75, negated_conjecture, (v1_xboole_0(k2_relat_1(esk11_0))), inference(sr,[status(thm)],[c_0_71, c_0_72])).
% 0.21/0.40  cnf(c_0_76, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_45])])).
% 0.21/0.40  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75])]), c_0_76]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 78
% 0.21/0.40  # Proof object clause steps            : 53
% 0.21/0.40  # Proof object formula steps           : 25
% 0.21/0.40  # Proof object conjectures             : 25
% 0.21/0.40  # Proof object clause conjectures      : 22
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 18
% 0.21/0.40  # Proof object initial formulas used   : 12
% 0.21/0.40  # Proof object generating inferences   : 22
% 0.21/0.40  # Proof object simplifying inferences  : 43
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 14
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 39
% 0.21/0.40  # Removed in clause preprocessing      : 3
% 0.21/0.40  # Initial clauses in saturation        : 36
% 0.21/0.40  # Processed clauses                    : 308
% 0.21/0.40  # ...of these trivial                  : 1
% 0.21/0.40  # ...subsumed                          : 79
% 0.21/0.40  # ...remaining for further processing  : 228
% 0.21/0.40  # Other redundant clauses eliminated   : 16
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 4
% 0.21/0.40  # Backward-rewritten                   : 16
% 0.21/0.40  # Generated clauses                    : 430
% 0.21/0.40  # ...of the previous two non-trivial   : 399
% 0.21/0.40  # Contextual simplify-reflections      : 15
% 0.21/0.40  # Paramodulations                      : 416
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 16
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 160
% 0.21/0.40  #    Positive orientable unit clauses  : 12
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 5
% 0.21/0.40  #    Non-unit-clauses                  : 143
% 0.21/0.40  # Current number of unprocessed clauses: 152
% 0.21/0.40  # ...number of literals in the above   : 688
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 56
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 3548
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 1239
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 94
% 0.21/0.40  # Unit Clause-clause subsumption calls : 123
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 8
% 0.21/0.40  # BW rewrite match successes           : 5
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 11777
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.048 s
% 0.21/0.40  # System time              : 0.008 s
% 0.21/0.40  # Total time               : 0.056 s
% 0.21/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
