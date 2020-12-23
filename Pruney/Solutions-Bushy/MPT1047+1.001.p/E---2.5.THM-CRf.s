%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1047+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:38 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 165 expanded)
%              Number of clauses        :   35 (  60 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  294 ( 880 expanded)
%              Number of equality atoms :   60 ( 183 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t164_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).

fof(t158_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t66_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,k1_tarski(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r2_relset_1(X1,k1_tarski(X2),X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_2)).

fof(d7_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( X4 = k5_partfun1(X1,X2,X3)
        <=> ! [X5] :
              ( r2_hidden(X5,X4)
            <=> ? [X6] :
                  ( v1_funct_1(X6)
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & X6 = X5
                  & v1_partfun1(X6,X1)
                  & r1_partfun1(X3,X6) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

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

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t143_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r1_partfun1(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,k1_tarski(X2))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
           => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_2])).

fof(c_0_10,plain,(
    ! [X45,X46,X47,X48] :
      ( ( v1_funct_1(X48)
        | ~ r2_hidden(X48,k5_partfun1(X45,X46,X47))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( v1_funct_2(X48,X45,X46)
        | ~ r2_hidden(X48,k5_partfun1(X45,X46,X47))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
        | ~ r2_hidden(X48,k5_partfun1(X45,X46,X47))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

fof(c_0_11,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk1_2(X17,X18),X18)
        | esk1_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk1_2(X17,X18),X18)
        | esk1_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X53,X54,X55,X56] :
      ( ~ v1_funct_1(X55)
      | ~ v1_funct_2(X55,X53,k1_tarski(X54))
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,k1_tarski(X54))))
      | ~ v1_funct_1(X56)
      | ~ v1_funct_2(X56,X53,k1_tarski(X54))
      | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,k1_tarski(X54))))
      | r2_relset_1(X53,k1_tarski(X54),X55,X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_2])])])).

fof(c_0_13,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))
    & k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) != k1_tarski(esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_18,plain,(
    ! [X20,X21,X22,X23,X24,X26,X27,X28,X30] :
      ( ( v1_funct_1(esk2_5(X20,X21,X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( m1_subset_1(esk2_5(X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( esk2_5(X20,X21,X22,X23,X24) = X24
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v1_partfun1(esk2_5(X20,X21,X22,X23,X24),X20)
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( r1_partfun1(X22,esk2_5(X20,X21,X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | X27 != X26
        | ~ v1_partfun1(X27,X20)
        | ~ r1_partfun1(X22,X27)
        | r2_hidden(X26,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ r2_hidden(esk3_4(X20,X21,X22,X28),X28)
        | ~ v1_funct_1(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | X30 != esk3_4(X20,X21,X22,X28)
        | ~ v1_partfun1(X30,X20)
        | ~ r1_partfun1(X22,X30)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v1_funct_1(esk4_4(X20,X21,X22,X28))
        | r2_hidden(esk3_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( m1_subset_1(esk4_4(X20,X21,X22,X28),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | r2_hidden(esk3_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( esk4_4(X20,X21,X22,X28) = esk3_4(X20,X21,X22,X28)
        | r2_hidden(esk3_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v1_partfun1(esk4_4(X20,X21,X22,X28),X20)
        | r2_hidden(esk3_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( r1_partfun1(X22,esk4_4(X20,X21,X22,X28))
        | r2_hidden(esk3_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_19,plain,(
    ! [X10,X11,X12] :
      ( ( v1_funct_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | v1_xboole_0(X11) )
      & ( v1_partfun1(X12,X10)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | v1_xboole_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_20,plain,(
    ! [X34] : ~ v1_xboole_0(k1_tarski(X34)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_21,plain,(
    ! [X41,X42,X43,X44] :
      ( ~ v1_funct_1(X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,k1_tarski(X42))))
      | ~ v1_funct_1(X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,k1_tarski(X42))))
      | r1_partfun1(X43,X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).

cnf(c_0_22,plain,
    ( r2_relset_1(X2,k1_tarski(X3),X1,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,k1_tarski(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,k1_tarski(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( esk1_2(X1,k5_partfun1(X2,X3,X4)) = X1
    | k5_partfun1(X2,X3,X4) = k1_tarski(X1)
    | v1_funct_2(esk1_2(X1,k5_partfun1(X2,X3,X4)),X2,X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( esk1_2(X1,k5_partfun1(X2,X3,X4)) = X1
    | k5_partfun1(X2,X3,X4) = k1_tarski(X1)
    | m1_subset_1(esk1_2(X1,k5_partfun1(X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_30,plain,
    ( esk1_2(X1,k5_partfun1(X2,X3,X4)) = X1
    | k5_partfun1(X2,X3,X4) = k1_tarski(X1)
    | v1_funct_1(esk1_2(X1,k5_partfun1(X2,X3,X4)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_31,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_35,plain,(
    ! [X35,X36,X37,X38] :
      ( ( ~ r2_relset_1(X35,X36,X37,X38)
        | X37 = X38
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X37 != X38
        | r2_relset_1(X35,X36,X37,X38)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_36,negated_conjecture,
    ( r2_relset_1(esk6_0,k1_tarski(esk7_0),X1,esk9_0)
    | ~ v1_funct_2(X1,esk6_0,k1_tarski(esk7_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_37,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)) = X1
    | k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) = k1_tarski(X1)
    | v1_funct_2(esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)),esk6_0,k1_tarski(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_38,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)) = X1
    | k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) = k1_tarski(X1)
    | m1_subset_1(esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_28])])).

cnf(c_0_39,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)) = X1
    | k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) = k1_tarski(X1)
    | v1_funct_1(esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_28])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_31])])).

cnf(c_0_41,negated_conjecture,
    ( v1_partfun1(esk9_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_23]),c_0_24]),c_0_25])]),c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r1_partfun1(X1,esk9_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_24])])).

cnf(c_0_43,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)) = X1
    | k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) = k1_tarski(X1)
    | r2_relset_1(esk6_0,k1_tarski(esk7_0),esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)),esk9_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk9_0,k5_partfun1(esk6_0,X1,X2))
    | ~ r1_partfun1(X2,esk9_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24])])).

cnf(c_0_46,negated_conjecture,
    ( r1_partfun1(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_28])])).

cnf(c_0_47,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)) = esk9_0
    | esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)) = X1
    | k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) = k1_tarski(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_25])]),c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) != k1_tarski(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk9_0,k5_partfun1(esk6_0,X1,esk8_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X1)))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_28])])).

cnf(c_0_50,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_51,negated_conjecture,
    ( esk1_2(esk9_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)) = esk9_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_47])]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk9_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_25]),c_0_27])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])]),c_0_48]),
    [proof]).

%------------------------------------------------------------------------------
