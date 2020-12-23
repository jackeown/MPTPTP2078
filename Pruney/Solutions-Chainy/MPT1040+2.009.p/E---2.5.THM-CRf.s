%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:07 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 422 expanded)
%              Number of clauses        :   49 ( 175 expanded)
%              Number of leaves         :   10 (  97 expanded)
%              Depth                    :   12
%              Number of atoms          :  268 (2619 expanded)
%              Number of equality atoms :   61 ( 540 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t155_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_partfun1(X3,X4)
           => ( ( X2 = k1_xboole_0
                & X1 != k1_xboole_0 )
              | r2_hidden(X4,k5_partfun1(X1,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_10,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X26,X27,X28,X29,X30,X32,X33,X34,X36] :
      ( ( v1_funct_1(esk2_5(X26,X27,X28,X29,X30))
        | ~ r2_hidden(X30,X29)
        | X29 != k5_partfun1(X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( m1_subset_1(esk2_5(X26,X27,X28,X29,X30),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ r2_hidden(X30,X29)
        | X29 != k5_partfun1(X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( esk2_5(X26,X27,X28,X29,X30) = X30
        | ~ r2_hidden(X30,X29)
        | X29 != k5_partfun1(X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v1_partfun1(esk2_5(X26,X27,X28,X29,X30),X26)
        | ~ r2_hidden(X30,X29)
        | X29 != k5_partfun1(X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( r1_partfun1(X28,esk2_5(X26,X27,X28,X29,X30))
        | ~ r2_hidden(X30,X29)
        | X29 != k5_partfun1(X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | X33 != X32
        | ~ v1_partfun1(X33,X26)
        | ~ r1_partfun1(X28,X33)
        | r2_hidden(X32,X29)
        | X29 != k5_partfun1(X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( ~ r2_hidden(esk3_4(X26,X27,X28,X34),X34)
        | ~ v1_funct_1(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | X36 != esk3_4(X26,X27,X28,X34)
        | ~ v1_partfun1(X36,X26)
        | ~ r1_partfun1(X28,X36)
        | X34 = k5_partfun1(X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v1_funct_1(esk4_4(X26,X27,X28,X34))
        | r2_hidden(esk3_4(X26,X27,X28,X34),X34)
        | X34 = k5_partfun1(X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( m1_subset_1(esk4_4(X26,X27,X28,X34),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | r2_hidden(esk3_4(X26,X27,X28,X34),X34)
        | X34 = k5_partfun1(X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( esk4_4(X26,X27,X28,X34) = esk3_4(X26,X27,X28,X34)
        | r2_hidden(esk3_4(X26,X27,X28,X34),X34)
        | X34 = k5_partfun1(X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v1_partfun1(esk4_4(X26,X27,X28,X34),X26)
        | r2_hidden(esk3_4(X26,X27,X28,X34),X34)
        | X34 = k5_partfun1(X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( r1_partfun1(X28,esk4_4(X26,X27,X28,X34))
        | r2_hidden(esk3_4(X26,X27,X28,X34),X34)
        | X34 = k5_partfun1(X26,X27,X28)
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_14,plain,(
    ! [X20,X21,X22] :
      ( ~ r2_hidden(X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | ~ v1_xboole_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( r1_partfun1(X3,X4)
             => ( ( X2 = k1_xboole_0
                  & X1 != k1_xboole_0 )
                | r2_hidden(X4,k5_partfun1(X1,X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t155_funct_2])).

cnf(c_0_18,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_22,plain,(
    ! [X23,X24,X25] :
      ( ( v1_funct_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | v1_xboole_0(X24) )
      & ( v1_partfun1(X25,X23)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | v1_xboole_0(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_23,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk5_0,esk6_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & r1_partfun1(esk7_0,esk8_0)
    & ( esk6_0 != k1_xboole_0
      | esk5_0 = k1_xboole_0 )
    & ~ r2_hidden(esk8_0,k5_partfun1(esk5_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_partfun1(X3,X4,X5)
    | ~ r1_partfun1(X5,X1)
    | ~ v1_partfun1(X1,X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X16,X17] :
      ( ( k2_zfmisc_1(X16,X17) != k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v1_partfun1(esk8_0,esk5_0)
    | v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk7_0))
    | ~ r1_partfun1(esk7_0,X1)
    | ~ v1_partfun1(X1,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_38,negated_conjecture,
    ( r1_partfun1(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k5_partfun1(esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_40,plain,(
    ! [X38] :
      ( v1_partfun1(k6_partfun1(X38),X38)
      & m1_subset_1(k6_partfun1(X38),k1_zfmisc_1(k2_zfmisc_1(X38,X38))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X15] :
      ( ~ r1_tarski(X15,k1_xboole_0)
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_43,negated_conjecture,
    ( v1_partfun1(esk8_0,esk5_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_partfun1(esk8_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_30]),c_0_28])]),c_0_39])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk6_0,X1) ),
    inference(sr,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_35])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_28])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_54,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = esk8_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[c_0_36,c_0_44])).

cnf(c_0_60,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_62,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_56]),c_0_58]),c_0_56]),c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_56])).

cnf(c_0_64,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_65,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_partfun1(esk8_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_68,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:17:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.20/0.45  # and selection function SelectNewComplexAHP.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.018 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.45  fof(d7_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(X4=k5_partfun1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>?[X6]:((((v1_funct_1(X6)&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&X6=X5)&v1_partfun1(X6,X1))&r1_partfun1(X3,X6))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_partfun1)).
% 0.20/0.45  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.45  fof(t155_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_2)).
% 0.20/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.45  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.20/0.45  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.45  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.20/0.45  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.45  fof(c_0_10, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.45  fof(c_0_11, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.45  cnf(c_0_12, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.45  fof(c_0_13, plain, ![X26, X27, X28, X29, X30, X32, X33, X34, X36]:(((((((v1_funct_1(esk2_5(X26,X27,X28,X29,X30))|~r2_hidden(X30,X29)|X29!=k5_partfun1(X26,X27,X28)|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&(m1_subset_1(esk2_5(X26,X27,X28,X29,X30),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|~r2_hidden(X30,X29)|X29!=k5_partfun1(X26,X27,X28)|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&(esk2_5(X26,X27,X28,X29,X30)=X30|~r2_hidden(X30,X29)|X29!=k5_partfun1(X26,X27,X28)|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&(v1_partfun1(esk2_5(X26,X27,X28,X29,X30),X26)|~r2_hidden(X30,X29)|X29!=k5_partfun1(X26,X27,X28)|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&(r1_partfun1(X28,esk2_5(X26,X27,X28,X29,X30))|~r2_hidden(X30,X29)|X29!=k5_partfun1(X26,X27,X28)|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|X33!=X32|~v1_partfun1(X33,X26)|~r1_partfun1(X28,X33)|r2_hidden(X32,X29)|X29!=k5_partfun1(X26,X27,X28)|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&((~r2_hidden(esk3_4(X26,X27,X28,X34),X34)|(~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|X36!=esk3_4(X26,X27,X28,X34)|~v1_partfun1(X36,X26)|~r1_partfun1(X28,X36))|X34=k5_partfun1(X26,X27,X28)|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&(((((v1_funct_1(esk4_4(X26,X27,X28,X34))|r2_hidden(esk3_4(X26,X27,X28,X34),X34)|X34=k5_partfun1(X26,X27,X28)|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&(m1_subset_1(esk4_4(X26,X27,X28,X34),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|r2_hidden(esk3_4(X26,X27,X28,X34),X34)|X34=k5_partfun1(X26,X27,X28)|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&(esk4_4(X26,X27,X28,X34)=esk3_4(X26,X27,X28,X34)|r2_hidden(esk3_4(X26,X27,X28,X34),X34)|X34=k5_partfun1(X26,X27,X28)|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&(v1_partfun1(esk4_4(X26,X27,X28,X34),X26)|r2_hidden(esk3_4(X26,X27,X28,X34),X34)|X34=k5_partfun1(X26,X27,X28)|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&(r1_partfun1(X28,esk4_4(X26,X27,X28,X34))|r2_hidden(esk3_4(X26,X27,X28,X34),X34)|X34=k5_partfun1(X26,X27,X28)|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).
% 0.20/0.45  fof(c_0_14, plain, ![X20, X21, X22]:(~r2_hidden(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X22))|~v1_xboole_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.45  cnf(c_0_15, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.45  cnf(c_0_16, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_12])).
% 0.20/0.45  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3))))))), inference(assume_negation,[status(cth)],[t155_funct_2])).
% 0.20/0.45  cnf(c_0_18, plain, (r2_hidden(X4,X6)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X1!=X4|~v1_partfun1(X1,X2)|~r1_partfun1(X5,X1)|X6!=k5_partfun1(X2,X3,X5)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.45  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.45  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.45  fof(c_0_21, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.45  fof(c_0_22, plain, ![X23, X24, X25]:((v1_funct_1(X25)|(~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|v1_xboole_0(X24))&(v1_partfun1(X25,X23)|(~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|v1_xboole_0(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.20/0.45  fof(c_0_23, negated_conjecture, ((v1_funct_1(esk7_0)&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r1_partfun1(esk7_0,esk8_0)&((esk6_0!=k1_xboole_0|esk5_0=k1_xboole_0)&~r2_hidden(esk8_0,k5_partfun1(esk5_0,esk6_0,esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.20/0.45  cnf(c_0_24, plain, (r2_hidden(X1,X2)|X2!=k5_partfun1(X3,X4,X5)|~r1_partfun1(X5,X1)|~v1_partfun1(X1,X3)|~v1_funct_1(X5)|~v1_funct_1(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.45  cnf(c_0_25, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.45  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  cnf(c_0_27, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.45  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.45  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.45  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.45  cnf(c_0_31, plain, (r2_hidden(X1,k5_partfun1(X2,X3,X4))|~r1_partfun1(X4,X1)|~v1_partfun1(X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.45  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.45  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.45  fof(c_0_34, plain, ![X16, X17]:((k2_zfmisc_1(X16,X17)!=k1_xboole_0|(X16=k1_xboole_0|X17=k1_xboole_0))&((X16!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0)&(X17!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.45  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.45  cnf(c_0_36, negated_conjecture, (v1_partfun1(esk8_0,esk5_0)|v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])])).
% 0.20/0.45  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk7_0))|~r1_partfun1(esk7_0,X1)|~v1_partfun1(X1,esk5_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.20/0.45  cnf(c_0_38, negated_conjecture, (r1_partfun1(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.45  cnf(c_0_39, negated_conjecture, (~r2_hidden(esk8_0,k5_partfun1(esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.45  fof(c_0_40, plain, ![X38]:(v1_partfun1(k6_partfun1(X38),X38)&m1_subset_1(k6_partfun1(X38),k1_zfmisc_1(k2_zfmisc_1(X38,X38)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.20/0.45  cnf(c_0_41, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.45  fof(c_0_42, plain, ![X15]:(~r1_tarski(X15,k1_xboole_0)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.45  cnf(c_0_43, negated_conjecture, (v1_partfun1(esk8_0,esk5_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.45  cnf(c_0_44, negated_conjecture, (~v1_partfun1(esk8_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_30]), c_0_28])]), c_0_39])).
% 0.20/0.45  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.45  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.45  cnf(c_0_47, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.45  cnf(c_0_48, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_41])).
% 0.20/0.45  cnf(c_0_49, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.45  cnf(c_0_50, negated_conjecture, (r1_tarski(esk6_0,X1)), inference(sr,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.45  cnf(c_0_51, plain, (X1=X2|~v1_xboole_0(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_35])).
% 0.20/0.45  cnf(c_0_52, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_46, c_0_28])).
% 0.20/0.45  cnf(c_0_53, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.45  cnf(c_0_54, plain, (m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.45  cnf(c_0_55, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.45  cnf(c_0_56, negated_conjecture, (esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.45  cnf(c_0_57, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=esk8_0|~v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.45  cnf(c_0_58, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_53])).
% 0.20/0.45  cnf(c_0_59, negated_conjecture, (v1_xboole_0(esk6_0)), inference(sr,[status(thm)],[c_0_36, c_0_44])).
% 0.20/0.45  cnf(c_0_60, plain, (r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_54])).
% 0.20/0.45  cnf(c_0_61, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 0.20/0.45  cnf(c_0_62, negated_conjecture, (esk8_0=k1_xboole_0|~v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_56]), c_0_58]), c_0_56]), c_0_58])).
% 0.20/0.45  cnf(c_0_63, negated_conjecture, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_59, c_0_56])).
% 0.20/0.45  cnf(c_0_64, plain, (v1_partfun1(k6_partfun1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.45  cnf(c_0_65, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_60])).
% 0.20/0.45  cnf(c_0_66, negated_conjecture, (~v1_partfun1(esk8_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_44, c_0_61])).
% 0.20/0.45  cnf(c_0_67, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 0.20/0.45  cnf(c_0_68, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.45  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_68])]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 70
% 0.20/0.45  # Proof object clause steps            : 49
% 0.20/0.45  # Proof object formula steps           : 21
% 0.20/0.45  # Proof object conjectures             : 26
% 0.20/0.45  # Proof object clause conjectures      : 23
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 21
% 0.20/0.45  # Proof object initial formulas used   : 10
% 0.20/0.45  # Proof object generating inferences   : 18
% 0.20/0.45  # Proof object simplifying inferences  : 26
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 10
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 37
% 0.20/0.45  # Removed in clause preprocessing      : 1
% 0.20/0.45  # Initial clauses in saturation        : 36
% 0.20/0.45  # Processed clauses                    : 775
% 0.20/0.45  # ...of these trivial                  : 2
% 0.20/0.45  # ...subsumed                          : 353
% 0.20/0.45  # ...remaining for further processing  : 420
% 0.20/0.45  # Other redundant clauses eliminated   : 17
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 21
% 0.20/0.45  # Backward-rewritten                   : 211
% 0.20/0.45  # Generated clauses                    : 1302
% 0.20/0.45  # ...of the previous two non-trivial   : 1464
% 0.20/0.45  # Contextual simplify-reflections      : 10
% 0.20/0.45  # Paramodulations                      : 1222
% 0.20/0.45  # Factorizations                       : 0
% 0.20/0.45  # Equation resolutions                 : 27
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 97
% 0.20/0.45  #    Positive orientable unit clauses  : 15
% 0.20/0.45  #    Positive unorientable unit clauses: 0
% 0.20/0.45  #    Negative unit clauses             : 0
% 0.20/0.45  #    Non-unit-clauses                  : 82
% 0.20/0.45  # Current number of unprocessed clauses: 740
% 0.20/0.45  # ...number of literals in the above   : 3573
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 320
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 44671
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 9142
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 384
% 0.20/0.45  # Unit Clause-clause subsumption calls : 553
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 12
% 0.20/0.45  # BW rewrite match successes           : 6
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 35476
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.104 s
% 0.20/0.45  # System time              : 0.004 s
% 0.20/0.45  # Total time               : 0.108 s
% 0.20/0.45  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
