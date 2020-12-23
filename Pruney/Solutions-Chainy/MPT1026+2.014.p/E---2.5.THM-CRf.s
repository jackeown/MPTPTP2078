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
% DateTime   : Thu Dec  3 11:06:45 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  128 (2472 expanded)
%              Number of clauses        :   93 (1258 expanded)
%              Number of leaves         :   18 ( 543 expanded)
%              Depth                    :   18
%              Number of atoms          :  438 (19580 expanded)
%              Number of equality atoms :   84 (7355 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_18,plain,(
    ! [X36,X37,X38,X39,X41,X42,X43,X44,X45,X47] :
      ( ( v1_relat_1(esk2_4(X36,X37,X38,X39))
        | ~ r2_hidden(X39,X38)
        | X38 != k1_funct_2(X36,X37) )
      & ( v1_funct_1(esk2_4(X36,X37,X38,X39))
        | ~ r2_hidden(X39,X38)
        | X38 != k1_funct_2(X36,X37) )
      & ( X39 = esk2_4(X36,X37,X38,X39)
        | ~ r2_hidden(X39,X38)
        | X38 != k1_funct_2(X36,X37) )
      & ( k1_relat_1(esk2_4(X36,X37,X38,X39)) = X36
        | ~ r2_hidden(X39,X38)
        | X38 != k1_funct_2(X36,X37) )
      & ( r1_tarski(k2_relat_1(esk2_4(X36,X37,X38,X39)),X37)
        | ~ r2_hidden(X39,X38)
        | X38 != k1_funct_2(X36,X37) )
      & ( ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42)
        | X41 != X42
        | k1_relat_1(X42) != X36
        | ~ r1_tarski(k2_relat_1(X42),X37)
        | r2_hidden(X41,X38)
        | X38 != k1_funct_2(X36,X37) )
      & ( ~ r2_hidden(esk3_3(X43,X44,X45),X45)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47)
        | esk3_3(X43,X44,X45) != X47
        | k1_relat_1(X47) != X43
        | ~ r1_tarski(k2_relat_1(X47),X44)
        | X45 = k1_funct_2(X43,X44) )
      & ( v1_relat_1(esk4_3(X43,X44,X45))
        | r2_hidden(esk3_3(X43,X44,X45),X45)
        | X45 = k1_funct_2(X43,X44) )
      & ( v1_funct_1(esk4_3(X43,X44,X45))
        | r2_hidden(esk3_3(X43,X44,X45),X45)
        | X45 = k1_funct_2(X43,X44) )
      & ( esk3_3(X43,X44,X45) = esk4_3(X43,X44,X45)
        | r2_hidden(esk3_3(X43,X44,X45),X45)
        | X45 = k1_funct_2(X43,X44) )
      & ( k1_relat_1(esk4_3(X43,X44,X45)) = X43
        | r2_hidden(esk3_3(X43,X44,X45),X45)
        | X45 = k1_funct_2(X43,X44) )
      & ( r1_tarski(k2_relat_1(esk4_3(X43,X44,X45)),X44)
        | r2_hidden(esk3_3(X43,X44,X45),X45)
        | X45 = k1_funct_2(X43,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_19,plain,
    ( k1_relat_1(esk2_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_20,plain,
    ( X1 = esk2_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_22,plain,
    ( v1_funct_1(esk2_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v1_relat_1(esk2_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k1_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( esk2_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_26,negated_conjecture,
    ( r2_hidden(esk8_0,k1_funct_2(esk6_0,esk7_0))
    & ( ~ v1_funct_1(esk8_0)
      | ~ v1_funct_2(esk8_0,esk6_0,esk7_0)
      | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_27,plain,
    ( v1_funct_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( v1_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X2,X5)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X2 != X1
    | k1_relat_1(X1) != X3
    | ~ r1_tarski(k2_relat_1(X1),X4)
    | X5 != k1_funct_2(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk8_0,k1_funct_2(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_33,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_relat_1(esk2_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_funct_2(k1_relat_1(X1),X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

fof(c_0_39,plain,(
    ! [X19,X20] :
      ( ( r1_tarski(k1_relat_1(X19),k1_relat_1(X20))
        | ~ r1_tarski(X19,X20)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r1_tarski(k2_relat_1(X19),k2_relat_1(X20))
        | ~ r1_tarski(X19,X20)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_40,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk8_0,k1_funct_2(esk6_0,X1))
    | ~ r1_tarski(k2_relat_1(esk8_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_44,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_45,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ r1_tarski(k1_relat_1(X29),X27)
      | ~ r1_tarski(k2_relat_1(X29),X28)
      | m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk8_0,k1_funct_2(esk6_0,k2_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_38])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( k2_relat_1(X1) = k2_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk8_0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_53,plain,(
    ! [X49] :
      ( ( v1_funct_1(X49)
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49) )
      & ( v1_funct_2(X49,k1_relat_1(X49),k2_relat_1(X49))
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49) )
      & ( m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X49),k2_relat_1(X49))))
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_54,plain,(
    ! [X13,X14] :
      ( ( k2_zfmisc_1(X13,X14) != k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_55,plain,(
    ! [X30,X31,X32] :
      ( ( v1_funct_1(X32)
        | ~ v1_funct_1(X32)
        | ~ v1_partfun1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v1_funct_2(X32,X30,X31)
        | ~ v1_funct_1(X32)
        | ~ v1_partfun1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( k2_relat_1(esk8_0) = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk8_0)
    | ~ r1_tarski(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_38])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_60,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_xboole_0(X24)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X24)))
      | v1_xboole_0(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_62,plain,(
    ! [X33,X34,X35] :
      ( ( v1_funct_1(X35)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | v1_xboole_0(X34) )
      & ( v1_partfun1(X35,X33)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_63,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_64,plain,(
    ! [X50,X51,X52] :
      ( ( v1_funct_1(X52)
        | r2_hidden(esk5_3(X50,X51,X52),X50)
        | k1_relat_1(X52) != X50
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( v1_funct_2(X52,X50,X51)
        | r2_hidden(esk5_3(X50,X51,X52),X50)
        | k1_relat_1(X52) != X50
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | r2_hidden(esk5_3(X50,X51,X52),X50)
        | k1_relat_1(X52) != X50
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( v1_funct_1(X52)
        | ~ r2_hidden(k1_funct_1(X52,esk5_3(X50,X51,X52)),X51)
        | k1_relat_1(X52) != X50
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( v1_funct_2(X52,X50,X51)
        | ~ r2_hidden(k1_funct_1(X52,esk5_3(X50,X51,X52)),X51)
        | k1_relat_1(X52) != X50
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | ~ r2_hidden(k1_funct_1(X52,esk5_3(X50,X51,X52)),X51)
        | k1_relat_1(X52) != X50
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_66,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | v1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_67,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_68,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(k2_relat_1(esk8_0),X2)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_36]),c_0_38])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),esk7_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk8_0)
    | ~ r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_73,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_75,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_77,plain,
    ( v1_funct_2(X1,X2,X3)
    | r2_hidden(esk5_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_78,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_79,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_80,plain,(
    ! [X17,X18] : v1_relat_1(k2_zfmisc_1(X17,X18)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_81,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_82,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_83,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(X1,esk7_0))
    | ~ r1_tarski(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_38]),c_0_72])])).

cnf(c_0_85,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_86,negated_conjecture,
    ( v1_partfun1(esk8_0,esk6_0)
    | v1_xboole_0(k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_74]),c_0_76]),c_0_37])])).

fof(c_0_87,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_88,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | r2_hidden(esk5_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_77])).

fof(c_0_89,plain,(
    ! [X10] :
      ( ~ v1_xboole_0(X10)
      | X10 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_90,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_78]),c_0_79])])).

cnf(c_0_91,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_92,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_93,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_funct_1(esk8_0)
    | ~ v1_funct_2(esk8_0,esk6_0,esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_95,negated_conjecture,
    ( v1_funct_2(esk8_0,X1,esk7_0)
    | ~ v1_partfun1(esk8_0,X1)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_37])])).

cnf(c_0_96,negated_conjecture,
    ( v1_partfun1(esk8_0,esk6_0)
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_97,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,X1)
    | r2_hidden(esk5_3(esk6_0,X1,esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_99,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_100,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_69])).

cnf(c_0_101,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_102,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_82])).

cnf(c_0_103,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_69])).

cnf(c_0_104,plain,
    ( k1_relat_1(X1) = k1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_93])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_funct_2(esk8_0,esk6_0,esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_37])])).

cnf(c_0_106,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk7_0)
    | v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_72])])).

cnf(c_0_107,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,X1)
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_108,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_109,plain,
    ( r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_101]),c_0_102])]),c_0_103])).

cnf(c_0_110,plain,
    ( k1_relat_1(X1) = k1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_104,c_0_93])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_74])).

cnf(c_0_112,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_113,negated_conjecture,
    ( ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_107])).

cnf(c_0_114,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_115,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0))) = esk6_0
    | ~ r1_tarski(k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_36]),c_0_91]),c_0_38])])).

cnf(c_0_116,negated_conjecture,
    ( v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_50]),c_0_38]),c_0_36]),c_0_72]),c_0_57])])).

cnf(c_0_117,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_82])).

cnf(c_0_118,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_119,negated_conjecture,
    ( ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
    | ~ r1_tarski(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_100])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(esk6_0,k1_xboole_0)
    | ~ r1_tarski(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_36])).

cnf(c_0_121,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0)),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_122,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_116])).

cnf(c_0_123,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_101]),c_0_102]),c_0_72]),c_0_118])])).

cnf(c_0_124,negated_conjecture,
    ( ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
    | ~ r1_tarski(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_125,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_122]),c_0_118]),c_0_78]),c_0_72]),c_0_122]),c_0_118]),c_0_78]),c_0_122]),c_0_72])])).

cnf(c_0_126,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_72])).

cnf(c_0_127,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_122]),c_0_122]),c_0_72])]),c_0_125]),c_0_82]),c_0_126])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:59:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.65  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.47/0.65  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.47/0.65  #
% 0.47/0.65  # Preprocessing time       : 0.029 s
% 0.47/0.65  # Presaturation interreduction done
% 0.47/0.65  
% 0.47/0.65  # Proof found!
% 0.47/0.65  # SZS status Theorem
% 0.47/0.65  # SZS output start CNFRefutation
% 0.47/0.65  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 0.47/0.65  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 0.47/0.65  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.47/0.65  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.47/0.65  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.47/0.65  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.47/0.65  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.47/0.65  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.47/0.65  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.47/0.65  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.47/0.65  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.47/0.65  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 0.47/0.65  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.47/0.65  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.47/0.65  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.47/0.65  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.47/0.65  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.47/0.65  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.47/0.65  fof(c_0_18, plain, ![X36, X37, X38, X39, X41, X42, X43, X44, X45, X47]:(((((((v1_relat_1(esk2_4(X36,X37,X38,X39))|~r2_hidden(X39,X38)|X38!=k1_funct_2(X36,X37))&(v1_funct_1(esk2_4(X36,X37,X38,X39))|~r2_hidden(X39,X38)|X38!=k1_funct_2(X36,X37)))&(X39=esk2_4(X36,X37,X38,X39)|~r2_hidden(X39,X38)|X38!=k1_funct_2(X36,X37)))&(k1_relat_1(esk2_4(X36,X37,X38,X39))=X36|~r2_hidden(X39,X38)|X38!=k1_funct_2(X36,X37)))&(r1_tarski(k2_relat_1(esk2_4(X36,X37,X38,X39)),X37)|~r2_hidden(X39,X38)|X38!=k1_funct_2(X36,X37)))&(~v1_relat_1(X42)|~v1_funct_1(X42)|X41!=X42|k1_relat_1(X42)!=X36|~r1_tarski(k2_relat_1(X42),X37)|r2_hidden(X41,X38)|X38!=k1_funct_2(X36,X37)))&((~r2_hidden(esk3_3(X43,X44,X45),X45)|(~v1_relat_1(X47)|~v1_funct_1(X47)|esk3_3(X43,X44,X45)!=X47|k1_relat_1(X47)!=X43|~r1_tarski(k2_relat_1(X47),X44))|X45=k1_funct_2(X43,X44))&(((((v1_relat_1(esk4_3(X43,X44,X45))|r2_hidden(esk3_3(X43,X44,X45),X45)|X45=k1_funct_2(X43,X44))&(v1_funct_1(esk4_3(X43,X44,X45))|r2_hidden(esk3_3(X43,X44,X45),X45)|X45=k1_funct_2(X43,X44)))&(esk3_3(X43,X44,X45)=esk4_3(X43,X44,X45)|r2_hidden(esk3_3(X43,X44,X45),X45)|X45=k1_funct_2(X43,X44)))&(k1_relat_1(esk4_3(X43,X44,X45))=X43|r2_hidden(esk3_3(X43,X44,X45),X45)|X45=k1_funct_2(X43,X44)))&(r1_tarski(k2_relat_1(esk4_3(X43,X44,X45)),X44)|r2_hidden(esk3_3(X43,X44,X45),X45)|X45=k1_funct_2(X43,X44))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.47/0.65  cnf(c_0_19, plain, (k1_relat_1(esk2_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_20, plain, (X1=esk2_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.47/0.65  cnf(c_0_22, plain, (v1_funct_1(esk2_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_23, plain, (v1_relat_1(esk2_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_24, plain, (k1_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.47/0.65  cnf(c_0_25, plain, (esk2_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.47/0.65  fof(c_0_26, negated_conjecture, (r2_hidden(esk8_0,k1_funct_2(esk6_0,esk7_0))&(~v1_funct_1(esk8_0)|~v1_funct_2(esk8_0,esk6_0,esk7_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.47/0.65  cnf(c_0_27, plain, (v1_funct_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_22])).
% 0.47/0.65  cnf(c_0_28, plain, (v1_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.47/0.65  cnf(c_0_29, plain, (r2_hidden(X2,X5)|~v1_relat_1(X1)|~v1_funct_1(X1)|X2!=X1|k1_relat_1(X1)!=X3|~r1_tarski(k2_relat_1(X1),X4)|X5!=k1_funct_2(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_30, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.47/0.65  cnf(c_0_31, negated_conjecture, (r2_hidden(esk8_0,k1_funct_2(esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.65  cnf(c_0_32, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 0.47/0.65  cnf(c_0_33, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_28, c_0_25])).
% 0.47/0.65  cnf(c_0_34, plain, (r1_tarski(k2_relat_1(esk2_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_35, plain, (r2_hidden(X1,k1_funct_2(k1_relat_1(X1),X2))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(er,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])])).
% 0.47/0.65  cnf(c_0_36, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.47/0.65  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk8_0)), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.47/0.65  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 0.47/0.65  fof(c_0_39, plain, ![X19, X20]:((r1_tarski(k1_relat_1(X19),k1_relat_1(X20))|~r1_tarski(X19,X20)|~v1_relat_1(X20)|~v1_relat_1(X19))&(r1_tarski(k2_relat_1(X19),k2_relat_1(X20))|~r1_tarski(X19,X20)|~v1_relat_1(X20)|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.47/0.65  fof(c_0_40, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.47/0.65  cnf(c_0_41, plain, (r1_tarski(k2_relat_1(esk2_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_34])).
% 0.47/0.65  cnf(c_0_42, negated_conjecture, (r2_hidden(esk8_0,k1_funct_2(esk6_0,X1))|~r1_tarski(k2_relat_1(esk8_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])])).
% 0.47/0.65  cnf(c_0_43, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.47/0.65  fof(c_0_44, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.47/0.65  fof(c_0_45, plain, ![X27, X28, X29]:(~v1_relat_1(X29)|(~r1_tarski(k1_relat_1(X29),X27)|~r1_tarski(k2_relat_1(X29),X28)|m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.47/0.65  cnf(c_0_46, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.47/0.65  cnf(c_0_47, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_41, c_0_25])).
% 0.47/0.65  cnf(c_0_48, negated_conjecture, (r2_hidden(esk8_0,k1_funct_2(esk6_0,k2_relat_1(X1)))|~v1_relat_1(X1)|~r1_tarski(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_38])])).
% 0.47/0.65  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.47/0.65  cnf(c_0_50, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.47/0.65  cnf(c_0_51, plain, (k2_relat_1(X1)=k2_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_46, c_0_43])).
% 0.47/0.65  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_relat_1(esk8_0),k2_relat_1(X1))|~v1_relat_1(X1)|~r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.47/0.65  fof(c_0_53, plain, ![X49]:(((v1_funct_1(X49)|(~v1_relat_1(X49)|~v1_funct_1(X49)))&(v1_funct_2(X49,k1_relat_1(X49),k2_relat_1(X49))|(~v1_relat_1(X49)|~v1_funct_1(X49))))&(m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X49),k2_relat_1(X49))))|(~v1_relat_1(X49)|~v1_funct_1(X49)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.47/0.65  fof(c_0_54, plain, ![X13, X14]:((k2_zfmisc_1(X13,X14)!=k1_xboole_0|(X13=k1_xboole_0|X14=k1_xboole_0))&((X13!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0)&(X14!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.47/0.65  fof(c_0_55, plain, ![X30, X31, X32]:((v1_funct_1(X32)|(~v1_funct_1(X32)|~v1_partfun1(X32,X30))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(v1_funct_2(X32,X30,X31)|(~v1_funct_1(X32)|~v1_partfun1(X32,X30))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.47/0.65  cnf(c_0_56, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.47/0.65  cnf(c_0_57, negated_conjecture, (r1_tarski(k2_relat_1(esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_47, c_0_31])).
% 0.47/0.65  cnf(c_0_58, negated_conjecture, (k2_relat_1(esk8_0)=k2_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,esk8_0)|~r1_tarski(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_38])])).
% 0.47/0.65  cnf(c_0_59, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.47/0.65  fof(c_0_60, plain, ![X24, X25, X26]:(~v1_xboole_0(X24)|(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X24)))|v1_xboole_0(X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.47/0.65  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.47/0.65  fof(c_0_62, plain, ![X33, X34, X35]:((v1_funct_1(X35)|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|v1_xboole_0(X34))&(v1_partfun1(X35,X33)|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|v1_xboole_0(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.47/0.65  cnf(c_0_63, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.47/0.65  fof(c_0_64, plain, ![X50, X51, X52]:((((v1_funct_1(X52)|(r2_hidden(esk5_3(X50,X51,X52),X50)|k1_relat_1(X52)!=X50)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(v1_funct_2(X52,X50,X51)|(r2_hidden(esk5_3(X50,X51,X52),X50)|k1_relat_1(X52)!=X50)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|(r2_hidden(esk5_3(X50,X51,X52),X50)|k1_relat_1(X52)!=X50)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(((v1_funct_1(X52)|(~r2_hidden(k1_funct_1(X52,esk5_3(X50,X51,X52)),X51)|k1_relat_1(X52)!=X50)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(v1_funct_2(X52,X50,X51)|(~r2_hidden(k1_funct_1(X52,esk5_3(X50,X51,X52)),X51)|k1_relat_1(X52)!=X50)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|(~r2_hidden(k1_funct_1(X52,esk5_3(X50,X51,X52)),X51)|k1_relat_1(X52)!=X50)|(~v1_relat_1(X52)|~v1_funct_1(X52))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.47/0.65  cnf(c_0_65, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.47/0.65  fof(c_0_66, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|v1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.47/0.65  cnf(c_0_67, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.47/0.65  cnf(c_0_68, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.47/0.65  cnf(c_0_69, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.47/0.65  cnf(c_0_70, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(X1,X2))|~r1_tarski(k2_relat_1(esk8_0),X2)|~r1_tarski(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_36]), c_0_38])])).
% 0.47/0.65  cnf(c_0_71, negated_conjecture, (r1_tarski(k2_relat_1(X1),esk7_0)|~v1_relat_1(X1)|~r1_tarski(X1,esk8_0)|~r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.47/0.65  cnf(c_0_72, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_59])).
% 0.47/0.65  cnf(c_0_73, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.47/0.65  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_36]), c_0_37]), c_0_38])])).
% 0.47/0.65  cnf(c_0_75, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.47/0.65  cnf(c_0_76, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_36]), c_0_37]), c_0_38])])).
% 0.47/0.65  cnf(c_0_77, plain, (v1_funct_2(X1,X2,X3)|r2_hidden(esk5_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.47/0.65  cnf(c_0_78, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_65])).
% 0.47/0.65  cnf(c_0_79, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.47/0.65  fof(c_0_80, plain, ![X17, X18]:v1_relat_1(k2_zfmisc_1(X17,X18)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.47/0.65  cnf(c_0_81, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.47/0.65  cnf(c_0_82, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_67])).
% 0.47/0.65  cnf(c_0_83, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.47/0.65  cnf(c_0_84, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(X1,esk7_0))|~r1_tarski(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_38]), c_0_72])])).
% 0.47/0.65  cnf(c_0_85, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.47/0.65  cnf(c_0_86, negated_conjecture, (v1_partfun1(esk8_0,esk6_0)|v1_xboole_0(k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_74]), c_0_76]), c_0_37])])).
% 0.47/0.65  fof(c_0_87, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.47/0.65  cnf(c_0_88, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|r2_hidden(esk5_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_77])).
% 0.47/0.65  fof(c_0_89, plain, ![X10]:(~v1_xboole_0(X10)|X10=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.47/0.65  cnf(c_0_90, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_78]), c_0_79])])).
% 0.47/0.65  cnf(c_0_91, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.47/0.65  cnf(c_0_92, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.47/0.65  cnf(c_0_93, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.47/0.65  cnf(c_0_94, negated_conjecture, (~v1_funct_1(esk8_0)|~v1_funct_2(esk8_0,esk6_0,esk7_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.65  cnf(c_0_95, negated_conjecture, (v1_funct_2(esk8_0,X1,esk7_0)|~v1_partfun1(esk8_0,X1)|~r1_tarski(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_37])])).
% 0.47/0.65  cnf(c_0_96, negated_conjecture, (v1_partfun1(esk8_0,esk6_0)|v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.47/0.65  cnf(c_0_97, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.47/0.65  cnf(c_0_98, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,X1)|r2_hidden(esk5_3(esk6_0,X1,esk8_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_36]), c_0_37]), c_0_38])])).
% 0.47/0.65  cnf(c_0_99, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.47/0.65  cnf(c_0_100, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_90, c_0_69])).
% 0.47/0.65  cnf(c_0_101, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.47/0.65  cnf(c_0_102, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_91, c_0_82])).
% 0.47/0.65  cnf(c_0_103, plain, (v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_92, c_0_69])).
% 0.47/0.65  cnf(c_0_104, plain, (k1_relat_1(X1)=k1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_46, c_0_93])).
% 0.47/0.65  cnf(c_0_105, negated_conjecture, (~v1_funct_2(esk8_0,esk6_0,esk7_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_37])])).
% 0.47/0.65  cnf(c_0_106, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk7_0)|v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_72])])).
% 0.47/0.65  cnf(c_0_107, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,X1)|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.47/0.65  cnf(c_0_108, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.47/0.65  cnf(c_0_109, plain, (r1_tarski(k1_relat_1(X1),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_101]), c_0_102])]), c_0_103])).
% 0.47/0.65  cnf(c_0_110, plain, (k1_relat_1(X1)=k1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_104, c_0_93])).
% 0.47/0.65  cnf(c_0_111, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0)))), inference(spm,[status(thm)],[c_0_49, c_0_74])).
% 0.47/0.65  cnf(c_0_112, negated_conjecture, (v1_xboole_0(esk8_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.47/0.65  cnf(c_0_113, negated_conjecture, (~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_105, c_0_107])).
% 0.47/0.65  cnf(c_0_114, plain, (k1_relat_1(X1)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.47/0.65  cnf(c_0_115, negated_conjecture, (k1_relat_1(k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0)))=esk6_0|~r1_tarski(k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_36]), c_0_91]), c_0_38])])).
% 0.47/0.65  cnf(c_0_116, negated_conjecture, (v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_50]), c_0_38]), c_0_36]), c_0_72]), c_0_57])])).
% 0.47/0.65  cnf(c_0_117, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_50, c_0_82])).
% 0.47/0.65  cnf(c_0_118, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.47/0.65  cnf(c_0_119, negated_conjecture, (~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))|~r1_tarski(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_113, c_0_100])).
% 0.47/0.65  cnf(c_0_120, negated_conjecture, (r1_tarski(esk6_0,k1_xboole_0)|~r1_tarski(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_109, c_0_36])).
% 0.47/0.65  cnf(c_0_121, negated_conjecture, (esk6_0=k1_xboole_0|~r1_tarski(k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0)),k1_xboole_0)|~r1_tarski(k2_zfmisc_1(esk6_0,k2_relat_1(esk8_0)),esk8_0)), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 0.47/0.65  cnf(c_0_122, negated_conjecture, (esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_99, c_0_116])).
% 0.47/0.65  cnf(c_0_123, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_101]), c_0_102]), c_0_72]), c_0_118])])).
% 0.47/0.65  cnf(c_0_124, negated_conjecture, (~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))|~r1_tarski(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 0.47/0.65  cnf(c_0_125, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_122]), c_0_118]), c_0_78]), c_0_72]), c_0_122]), c_0_118]), c_0_78]), c_0_122]), c_0_72])])).
% 0.47/0.65  cnf(c_0_126, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_123, c_0_72])).
% 0.47/0.65  cnf(c_0_127, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_122]), c_0_122]), c_0_72])]), c_0_125]), c_0_82]), c_0_126])]), ['proof']).
% 0.47/0.65  # SZS output end CNFRefutation
% 0.47/0.65  # Proof object total steps             : 128
% 0.47/0.65  # Proof object clause steps            : 93
% 0.47/0.65  # Proof object formula steps           : 35
% 0.47/0.65  # Proof object conjectures             : 38
% 0.47/0.65  # Proof object clause conjectures      : 35
% 0.47/0.65  # Proof object formula conjectures     : 3
% 0.47/0.65  # Proof object initial clauses used    : 30
% 0.47/0.65  # Proof object initial formulas used   : 18
% 0.47/0.65  # Proof object generating inferences   : 50
% 0.47/0.65  # Proof object simplifying inferences  : 78
% 0.47/0.65  # Training examples: 0 positive, 0 negative
% 0.47/0.65  # Parsed axioms                        : 18
% 0.47/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.65  # Initial clauses                      : 47
% 0.47/0.65  # Removed in clause preprocessing      : 5
% 0.47/0.65  # Initial clauses in saturation        : 42
% 0.47/0.65  # Processed clauses                    : 3283
% 0.47/0.65  # ...of these trivial                  : 9
% 0.47/0.65  # ...subsumed                          : 2183
% 0.47/0.65  # ...remaining for further processing  : 1090
% 0.47/0.65  # Other redundant clauses eliminated   : 29
% 0.47/0.65  # Clauses deleted for lack of memory   : 0
% 0.47/0.65  # Backward-subsumed                    : 44
% 0.47/0.65  # Backward-rewritten                   : 485
% 0.47/0.65  # Generated clauses                    : 12783
% 0.47/0.65  # ...of the previous two non-trivial   : 11791
% 0.47/0.65  # Contextual simplify-reflections      : 232
% 0.47/0.65  # Paramodulations                      : 12739
% 0.47/0.65  # Factorizations                       : 17
% 0.47/0.65  # Equation resolutions                 : 29
% 0.47/0.65  # Propositional unsat checks           : 0
% 0.47/0.65  #    Propositional check models        : 0
% 0.47/0.65  #    Propositional check unsatisfiable : 0
% 0.47/0.65  #    Propositional clauses             : 0
% 0.47/0.65  #    Propositional clauses after purity: 0
% 0.47/0.65  #    Propositional unsat core size     : 0
% 0.47/0.65  #    Propositional preprocessing time  : 0.000
% 0.47/0.65  #    Propositional encoding time       : 0.000
% 0.47/0.65  #    Propositional solver time         : 0.000
% 0.47/0.65  #    Success case prop preproc time    : 0.000
% 0.47/0.65  #    Success case prop encoding time   : 0.000
% 0.47/0.65  #    Success case prop solver time     : 0.000
% 0.47/0.65  # Current number of processed clauses  : 505
% 0.47/0.65  #    Positive orientable unit clauses  : 11
% 0.47/0.65  #    Positive unorientable unit clauses: 0
% 0.47/0.65  #    Negative unit clauses             : 2
% 0.47/0.65  #    Non-unit-clauses                  : 492
% 0.47/0.65  # Current number of unprocessed clauses: 8570
% 0.47/0.65  # ...number of literals in the above   : 39411
% 0.47/0.65  # Current number of archived formulas  : 0
% 0.47/0.65  # Current number of archived clauses   : 570
% 0.47/0.65  # Clause-clause subsumption calls (NU) : 156699
% 0.47/0.65  # Rec. Clause-clause subsumption calls : 52519
% 0.47/0.65  # Non-unit clause-clause subsumptions  : 2443
% 0.47/0.65  # Unit Clause-clause subsumption calls : 841
% 0.47/0.65  # Rewrite failures with RHS unbound    : 0
% 0.47/0.65  # BW rewrite match attempts            : 8
% 0.47/0.65  # BW rewrite match successes           : 6
% 0.47/0.65  # Condensation attempts                : 0
% 0.47/0.65  # Condensation successes               : 0
% 0.47/0.65  # Termbank termtop insertions          : 220732
% 0.47/0.65  
% 0.47/0.65  # -------------------------------------------------
% 0.47/0.65  # User time                : 0.302 s
% 0.47/0.65  # System time              : 0.013 s
% 0.47/0.65  # Total time               : 0.316 s
% 0.47/0.65  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
