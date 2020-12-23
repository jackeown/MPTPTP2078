%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:34 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 800 expanded)
%              Number of clauses        :   97 ( 363 expanded)
%              Number of leaves         :   16 ( 201 expanded)
%              Depth                    :   25
%              Number of atoms          :  450 (3309 expanded)
%              Number of equality atoms :  269 (1062 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t87_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k1_zfmisc_1(X1))
     => ! [X6] :
          ( m1_subset_1(X6,k1_zfmisc_1(X2))
         => ! [X7] :
              ( m1_subset_1(X7,k1_zfmisc_1(X3))
             => ! [X8] :
                  ( m1_subset_1(X8,k1_zfmisc_1(X4))
                 => ! [X9] :
                      ( m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))
                     => ( r2_hidden(X9,k4_zfmisc_1(X5,X6,X7,X8))
                       => ( r2_hidden(k8_mcart_1(X1,X2,X3,X4,X9),X5)
                          & r2_hidden(k9_mcart_1(X1,X2,X3,X4,X9),X6)
                          & r2_hidden(k10_mcart_1(X1,X2,X3,X4,X9),X7)
                          & r2_hidden(k11_mcart_1(X1,X2,X3,X4,X9),X8) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_mcart_1)).

fof(t60_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => ( ( r2_hidden(X3,X2)
          & X1 != X3 )
        | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(dt_k10_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(t61_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                & k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                & k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
                & k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(t67_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(dt_k8_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(dt_k11_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(dt_k9_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_16,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X26,X25)
        | r2_hidden(X26,X25)
        | v1_xboole_0(X25) )
      & ( ~ r2_hidden(X26,X25)
        | m1_subset_1(X26,X25)
        | v1_xboole_0(X25) )
      & ( ~ m1_subset_1(X26,X25)
        | v1_xboole_0(X26)
        | ~ v1_xboole_0(X25) )
      & ( ~ v1_xboole_0(X26)
        | m1_subset_1(X26,X25)
        | ~ v1_xboole_0(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_17,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v1_xboole_0(X10)
        | ~ r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_1(X12),X12)
        | v1_xboole_0(X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k1_zfmisc_1(X1))
       => ! [X6] :
            ( m1_subset_1(X6,k1_zfmisc_1(X2))
           => ! [X7] :
                ( m1_subset_1(X7,k1_zfmisc_1(X3))
               => ! [X8] :
                    ( m1_subset_1(X8,k1_zfmisc_1(X4))
                   => ! [X9] :
                        ( m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))
                       => ( r2_hidden(X9,k4_zfmisc_1(X5,X6,X7,X8))
                         => ( r2_hidden(k8_mcart_1(X1,X2,X3,X4,X9),X5)
                            & r2_hidden(k9_mcart_1(X1,X2,X3,X4,X9),X6)
                            & r2_hidden(k10_mcart_1(X1,X2,X3,X4,X9),X7)
                            & r2_hidden(k11_mcart_1(X1,X2,X3,X4,X9),X8) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t87_mcart_1])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(esk5_0))
    & m1_subset_1(esk10_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0))
    & r2_hidden(esk10_0,k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0))
    & ( ~ r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)
      | ~ r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)
      | ~ r2_hidden(k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk8_0)
      | ~ r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_22,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(X22,X21)
        | k3_xboole_0(k2_tarski(X20,X22),X21) = k1_tarski(X20)
        | ~ r2_hidden(X20,X21) )
      & ( X20 != X22
        | k3_xboole_0(k2_tarski(X20,X22),X21) = k1_tarski(X20)
        | ~ r2_hidden(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X29,X30,X31,X32,X33] :
      ( ~ m1_subset_1(X33,k4_zfmisc_1(X29,X30,X31,X32))
      | m1_subset_1(k10_mcart_1(X29,X30,X31,X32,X33),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk10_0,k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X53,X54,X55,X56,X57] :
      ( ( k8_mcart_1(X53,X54,X55,X56,X57) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X57)))
        | ~ m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 )
      & ( k9_mcart_1(X53,X54,X55,X56,X57) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X57)))
        | ~ m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 )
      & ( k10_mcart_1(X53,X54,X55,X56,X57) = k2_mcart_1(k1_mcart_1(X57))
        | ~ m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 )
      & ( k11_mcart_1(X53,X54,X55,X56,X57) = k2_mcart_1(X57)
        | ~ m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).

fof(c_0_27,plain,(
    ! [X18,X19] :
      ( ( k4_xboole_0(k1_tarski(X18),X19) != k1_xboole_0
        | r2_hidden(X18,X19) )
      & ( ~ r2_hidden(X18,X19)
        | k4_xboole_0(k1_tarski(X18),X19) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

cnf(c_0_28,plain,
    ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X49,X50,X51,X52] :
      ( ( X49 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 = k1_xboole_0
        | k4_zfmisc_1(X49,X50,X51,X52) != k1_xboole_0 )
      & ( X49 != k1_xboole_0
        | k4_zfmisc_1(X49,X50,X51,X52) = k1_xboole_0 )
      & ( X50 != k1_xboole_0
        | k4_zfmisc_1(X49,X50,X51,X52) = k1_xboole_0 )
      & ( X51 != k1_xboole_0
        | k4_zfmisc_1(X49,X50,X51,X52) = k1_xboole_0 )
      & ( X52 != k1_xboole_0
        | k4_zfmisc_1(X49,X50,X51,X52) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

fof(c_0_33,plain,(
    ! [X23,X24] :
      ( ( k4_xboole_0(k1_tarski(X23),X24) != k1_tarski(X23)
        | ~ r2_hidden(X23,X24) )
      & ( r2_hidden(X23,X24)
        | k4_xboole_0(k1_tarski(X23),X24) = k1_tarski(X23) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_zfmisc_1])])])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X39,X40,X41,X42,X43] :
      ( ~ m1_subset_1(X43,k4_zfmisc_1(X39,X40,X41,X42))
      | m1_subset_1(k8_mcart_1(X39,X40,X41,X42,X43),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( k3_xboole_0(k2_tarski(X1,X1),X2) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k10_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k10_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0) = k2_mcart_1(k1_mcart_1(esk10_0))
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_40,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X16] : k3_xboole_0(X16,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk10_0),k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_44,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k1_tarski(esk1_1(X1)),X1) = k1_xboole_0
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk10_0,esk10_0),k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)) = k1_tarski(esk10_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,plain,
    ( k4_zfmisc_1(X1,X2,X3,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( k1_tarski(esk10_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_25])])).

fof(c_0_53,plain,(
    ! [X17] :
      ( ~ v1_xboole_0(X17)
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_54,plain,(
    ! [X34,X35,X36,X37,X38] :
      ( ~ m1_subset_1(X38,k4_zfmisc_1(X34,X35,X36,X37))
      | m1_subset_1(k11_mcart_1(X34,X35,X36,X37,X38),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k8_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_30])).

cnf(c_0_56,negated_conjecture,
    ( k8_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0)))
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_30])).

cnf(c_0_57,plain,
    ( k3_xboole_0(k2_tarski(esk1_1(X1),esk1_1(X1)),X1) = k1_tarski(esk1_1(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | k1_tarski(esk1_1(X1)) != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_46]),c_0_36])).

fof(c_0_59,plain,(
    ! [X44,X45,X46,X47,X48] :
      ( ~ m1_subset_1(X48,k4_zfmisc_1(X44,X45,X46,X47))
      | m1_subset_1(k9_mcart_1(X44,X45,X46,X47,X48),X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)
    | ~ r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)
    | ~ r2_hidden(k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk8_0)
    | ~ r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_61,negated_conjecture,
    ( k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0) = k2_mcart_1(k1_mcart_1(esk10_0))
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_47])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_67,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_57]),c_0_58])).

cnf(c_0_69,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_70,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_72,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | ~ r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0)
    | ~ r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)
    | ~ r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)
    | ~ r2_hidden(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_74,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k11_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_30])).

cnf(c_0_76,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_50]),c_0_68])])).

cnf(c_0_77,plain,
    ( k4_zfmisc_1(X1,X2,k1_xboole_0,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( k4_zfmisc_1(X2,X1,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k9_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_30])).

cnf(c_0_80,negated_conjecture,
    ( k9_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0)))
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_30])).

cnf(c_0_81,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | ~ r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0)
    | ~ r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)
    | ~ r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0) = k2_mcart_1(esk10_0)
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_47])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(k11_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),esk9_0)
    | v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( k11_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0) = k2_mcart_1(esk10_0)
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_30])).

cnf(c_0_85,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_76]),c_0_77]),c_0_68])])).

cnf(c_0_86,plain,
    ( k4_zfmisc_1(X1,k1_xboole_0,X2,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | ~ r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)
    | ~ r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)
    | ~ r2_hidden(k2_mcart_1(esk10_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(k2_mcart_1(esk10_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_64])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_85]),c_0_86]),c_0_68])])).

cnf(c_0_91,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_87]),c_0_50]),c_0_68])])).

cnf(c_0_92,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | ~ r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)
    | ~ r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0)))
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_47])).

cnf(c_0_94,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_90]),c_0_64])).

cnf(c_0_95,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_91]),c_0_77]),c_0_68])])).

cnf(c_0_96,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | ~ r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0)))
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_47])).

cnf(c_0_98,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_95]),c_0_64])).

cnf(c_0_99,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])).

fof(c_0_100,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_101,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_99]),c_0_50]),c_0_68])])).

fof(c_0_102,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k3_xboole_0(X14,X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_103,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_105,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_101]),c_0_77]),c_0_68])])).

cnf(c_0_106,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_107,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(esk9_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_105]),c_0_86]),c_0_68])])).

cnf(c_0_110,plain,
    ( k4_zfmisc_1(k1_xboole_0,X1,X2,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_112,negated_conjecture,
    ( k3_xboole_0(esk9_0,esk5_0) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_109]),c_0_110]),c_0_68])])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(esk8_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_51])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_117,negated_conjecture,
    ( k3_xboole_0(esk8_0,esk4_0) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_107,c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_115]),c_0_50]),c_0_68])])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(esk7_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_116])).

cnf(c_0_120,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_51])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_122,negated_conjecture,
    ( k3_xboole_0(esk7_0,esk3_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_107,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_120]),c_0_77]),c_0_68])])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(esk6_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_121])).

cnf(c_0_125,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_51])).

cnf(c_0_126,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk2_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_107,c_0_124])).

cnf(c_0_127,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_125]),c_0_86]),c_0_68])])).

cnf(c_0_128,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_127]),c_0_51])).

cnf(c_0_129,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_128]),c_0_110]),c_0_51]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.43  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.028 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.43  fof(t87_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k1_zfmisc_1(X1))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X2))=>![X7]:(m1_subset_1(X7,k1_zfmisc_1(X3))=>![X8]:(m1_subset_1(X8,k1_zfmisc_1(X4))=>![X9]:(m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))=>(r2_hidden(X9,k4_zfmisc_1(X5,X6,X7,X8))=>(((r2_hidden(k8_mcart_1(X1,X2,X3,X4,X9),X5)&r2_hidden(k9_mcart_1(X1,X2,X3,X4,X9),X6))&r2_hidden(k10_mcart_1(X1,X2,X3,X4,X9),X7))&r2_hidden(k11_mcart_1(X1,X2,X3,X4,X9),X8)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_mcart_1)).
% 0.19/0.43  fof(t60_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 0.19/0.43  fof(dt_k10_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_mcart_1)).
% 0.19/0.43  fof(t61_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 0.19/0.43  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 0.19/0.43  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.19/0.43  fof(t67_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 0.19/0.43  fof(dt_k8_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_mcart_1)).
% 0.19/0.43  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.43  fof(t6_boole, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 0.19/0.43  fof(dt_k11_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_mcart_1)).
% 0.19/0.43  fof(dt_k9_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 0.19/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.43  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.43  fof(c_0_16, plain, ![X25, X26]:(((~m1_subset_1(X26,X25)|r2_hidden(X26,X25)|v1_xboole_0(X25))&(~r2_hidden(X26,X25)|m1_subset_1(X26,X25)|v1_xboole_0(X25)))&((~m1_subset_1(X26,X25)|v1_xboole_0(X26)|~v1_xboole_0(X25))&(~v1_xboole_0(X26)|m1_subset_1(X26,X25)|~v1_xboole_0(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.43  fof(c_0_17, plain, ![X10, X11, X12]:((~v1_xboole_0(X10)|~r2_hidden(X11,X10))&(r2_hidden(esk1_1(X12),X12)|v1_xboole_0(X12))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.43  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k1_zfmisc_1(X1))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X2))=>![X7]:(m1_subset_1(X7,k1_zfmisc_1(X3))=>![X8]:(m1_subset_1(X8,k1_zfmisc_1(X4))=>![X9]:(m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))=>(r2_hidden(X9,k4_zfmisc_1(X5,X6,X7,X8))=>(((r2_hidden(k8_mcart_1(X1,X2,X3,X4,X9),X5)&r2_hidden(k9_mcart_1(X1,X2,X3,X4,X9),X6))&r2_hidden(k10_mcart_1(X1,X2,X3,X4,X9),X7))&r2_hidden(k11_mcart_1(X1,X2,X3,X4,X9),X8))))))))), inference(assume_negation,[status(cth)],[t87_mcart_1])).
% 0.19/0.43  cnf(c_0_19, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.43  cnf(c_0_20, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.43  fof(c_0_21, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk9_0,k1_zfmisc_1(esk5_0))&(m1_subset_1(esk10_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0))&(r2_hidden(esk10_0,k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0))&(~r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)|~r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)|~r2_hidden(k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk8_0)|~r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.19/0.43  fof(c_0_22, plain, ![X20, X21, X22]:((r2_hidden(X22,X21)|k3_xboole_0(k2_tarski(X20,X22),X21)=k1_tarski(X20)|~r2_hidden(X20,X21))&(X20!=X22|k3_xboole_0(k2_tarski(X20,X22),X21)=k1_tarski(X20)|~r2_hidden(X20,X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).
% 0.19/0.43  fof(c_0_23, plain, ![X29, X30, X31, X32, X33]:(~m1_subset_1(X33,k4_zfmisc_1(X29,X30,X31,X32))|m1_subset_1(k10_mcart_1(X29,X30,X31,X32,X33),X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).
% 0.19/0.43  cnf(c_0_24, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.43  cnf(c_0_25, negated_conjecture, (r2_hidden(esk10_0,k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  fof(c_0_26, plain, ![X53, X54, X55, X56, X57]:((((k8_mcart_1(X53,X54,X55,X56,X57)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X57)))|~m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))|(X53=k1_xboole_0|X54=k1_xboole_0|X55=k1_xboole_0|X56=k1_xboole_0))&(k9_mcart_1(X53,X54,X55,X56,X57)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X57)))|~m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))|(X53=k1_xboole_0|X54=k1_xboole_0|X55=k1_xboole_0|X56=k1_xboole_0)))&(k10_mcart_1(X53,X54,X55,X56,X57)=k2_mcart_1(k1_mcart_1(X57))|~m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))|(X53=k1_xboole_0|X54=k1_xboole_0|X55=k1_xboole_0|X56=k1_xboole_0)))&(k11_mcart_1(X53,X54,X55,X56,X57)=k2_mcart_1(X57)|~m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))|(X53=k1_xboole_0|X54=k1_xboole_0|X55=k1_xboole_0|X56=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).
% 0.19/0.43  fof(c_0_27, plain, ![X18, X19]:((k4_xboole_0(k1_tarski(X18),X19)!=k1_xboole_0|r2_hidden(X18,X19))&(~r2_hidden(X18,X19)|k4_xboole_0(k1_tarski(X18),X19)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 0.19/0.43  cnf(c_0_28, plain, (k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.43  cnf(c_0_29, plain, (m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.43  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk10_0,k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.43  cnf(c_0_31, plain, (k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.43  fof(c_0_32, plain, ![X49, X50, X51, X52]:((X49=k1_xboole_0|X50=k1_xboole_0|X51=k1_xboole_0|X52=k1_xboole_0|k4_zfmisc_1(X49,X50,X51,X52)!=k1_xboole_0)&((((X49!=k1_xboole_0|k4_zfmisc_1(X49,X50,X51,X52)=k1_xboole_0)&(X50!=k1_xboole_0|k4_zfmisc_1(X49,X50,X51,X52)=k1_xboole_0))&(X51!=k1_xboole_0|k4_zfmisc_1(X49,X50,X51,X52)=k1_xboole_0))&(X52!=k1_xboole_0|k4_zfmisc_1(X49,X50,X51,X52)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.19/0.43  fof(c_0_33, plain, ![X23, X24]:((k4_xboole_0(k1_tarski(X23),X24)!=k1_tarski(X23)|~r2_hidden(X23,X24))&(r2_hidden(X23,X24)|k4_xboole_0(k1_tarski(X23),X24)=k1_tarski(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_zfmisc_1])])])).
% 0.19/0.43  cnf(c_0_34, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.43  fof(c_0_35, plain, ![X39, X40, X41, X42, X43]:(~m1_subset_1(X43,k4_zfmisc_1(X39,X40,X41,X42))|m1_subset_1(k8_mcart_1(X39,X40,X41,X42,X43),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).
% 0.19/0.43  cnf(c_0_36, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.43  cnf(c_0_37, plain, (k3_xboole_0(k2_tarski(X1,X1),X2)=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_28])).
% 0.19/0.43  cnf(c_0_38, negated_conjecture, (m1_subset_1(k10_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.43  cnf(c_0_39, negated_conjecture, (k10_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)=k2_mcart_1(k1_mcart_1(esk10_0))|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.19/0.43  cnf(c_0_40, plain, (k4_zfmisc_1(X2,X3,X4,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  fof(c_0_41, plain, ![X16]:k3_xboole_0(X16,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.43  cnf(c_0_42, plain, (k4_xboole_0(k1_tarski(X1),X2)!=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  cnf(c_0_43, negated_conjecture, (k4_xboole_0(k1_tarski(esk10_0),k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 0.19/0.43  cnf(c_0_44, plain, (m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.43  cnf(c_0_45, plain, (k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.43  cnf(c_0_46, plain, (k4_xboole_0(k1_tarski(esk1_1(X1)),X1)=k1_xboole_0|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 0.19/0.43  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk10_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_48, negated_conjecture, (k3_xboole_0(k2_tarski(esk10_0,esk10_0),k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0))=k1_tarski(esk10_0)), inference(spm,[status(thm)],[c_0_37, c_0_25])).
% 0.19/0.43  cnf(c_0_49, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|m1_subset_1(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.43  cnf(c_0_50, plain, (k4_zfmisc_1(X1,X2,X3,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_40])).
% 0.19/0.43  cnf(c_0_51, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.43  cnf(c_0_52, negated_conjecture, (k1_tarski(esk10_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_25])])).
% 0.19/0.43  fof(c_0_53, plain, ![X17]:(~v1_xboole_0(X17)|X17=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).
% 0.19/0.43  fof(c_0_54, plain, ![X34, X35, X36, X37, X38]:(~m1_subset_1(X38,k4_zfmisc_1(X34,X35,X36,X37))|m1_subset_1(k11_mcart_1(X34,X35,X36,X37,X38),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).
% 0.19/0.43  cnf(c_0_55, negated_conjecture, (m1_subset_1(k8_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),esk6_0)), inference(spm,[status(thm)],[c_0_44, c_0_30])).
% 0.19/0.43  cnf(c_0_56, negated_conjecture, (k8_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0)))|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_30])).
% 0.19/0.43  cnf(c_0_57, plain, (k3_xboole_0(k2_tarski(esk1_1(X1),esk1_1(X1)),X1)=k1_tarski(esk1_1(X1))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 0.19/0.43  cnf(c_0_58, plain, (v1_xboole_0(X1)|k1_tarski(esk1_1(X1))!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_46]), c_0_36])).
% 0.19/0.43  fof(c_0_59, plain, ![X44, X45, X46, X47, X48]:(~m1_subset_1(X48,k4_zfmisc_1(X44,X45,X46,X47))|m1_subset_1(k9_mcart_1(X44,X45,X46,X47,X48),X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).
% 0.19/0.43  cnf(c_0_60, negated_conjecture, (~r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)|~r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)|~r2_hidden(k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk8_0)|~r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_61, negated_conjecture, (k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0)=k2_mcart_1(k1_mcart_1(esk10_0))|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_47])).
% 0.19/0.43  cnf(c_0_62, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.43  cnf(c_0_63, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|m1_subset_1(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.43  cnf(c_0_64, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.43  cnf(c_0_65, plain, (m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.43  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_20, c_0_25])).
% 0.19/0.43  cnf(c_0_67, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.43  cnf(c_0_68, plain, (v1_xboole_0(k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_57]), c_0_58])).
% 0.19/0.43  cnf(c_0_69, plain, (k4_zfmisc_1(X2,X3,X1,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  cnf(c_0_70, plain, (m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.43  cnf(c_0_71, plain, (k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.43  cnf(c_0_72, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|~r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0)|~r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)|~r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)|~r2_hidden(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.43  cnf(c_0_73, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.19/0.43  cnf(c_0_74, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.43  cnf(c_0_75, negated_conjecture, (m1_subset_1(k11_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),esk9_0)), inference(spm,[status(thm)],[c_0_65, c_0_30])).
% 0.19/0.43  cnf(c_0_76, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_50]), c_0_68])])).
% 0.19/0.43  cnf(c_0_77, plain, (k4_zfmisc_1(X1,X2,k1_xboole_0,X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_69])).
% 0.19/0.43  cnf(c_0_78, plain, (k4_zfmisc_1(X2,X1,X3,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  cnf(c_0_79, negated_conjecture, (m1_subset_1(k9_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),esk7_0)), inference(spm,[status(thm)],[c_0_70, c_0_30])).
% 0.19/0.43  cnf(c_0_80, negated_conjecture, (k9_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)=k2_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0)))|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_30])).
% 0.19/0.43  cnf(c_0_81, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|~r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0)|~r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)|~r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.43  cnf(c_0_82, negated_conjecture, (k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0)=k2_mcart_1(esk10_0)|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_47])).
% 0.19/0.43  cnf(c_0_83, negated_conjecture, (r2_hidden(k11_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),esk9_0)|v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_62, c_0_75])).
% 0.19/0.43  cnf(c_0_84, negated_conjecture, (k11_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)=k2_mcart_1(esk10_0)|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_30])).
% 0.19/0.43  cnf(c_0_85, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_76]), c_0_77]), c_0_68])])).
% 0.19/0.43  cnf(c_0_86, plain, (k4_zfmisc_1(X1,k1_xboole_0,X2,X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_78])).
% 0.19/0.43  cnf(c_0_87, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk7_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.43  cnf(c_0_88, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|~r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)|~r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)|~r2_hidden(k2_mcart_1(esk10_0),esk9_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.43  cnf(c_0_89, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(k2_mcart_1(esk10_0),esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_64])).
% 0.19/0.43  cnf(c_0_90, negated_conjecture, (esk6_0=k1_xboole_0|m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_85]), c_0_86]), c_0_68])])).
% 0.19/0.43  cnf(c_0_91, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_87]), c_0_50]), c_0_68])])).
% 0.19/0.43  cnf(c_0_92, negated_conjecture, (esk9_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|~r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)|~r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.43  cnf(c_0_93, negated_conjecture, (k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0)=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0)))|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_47])).
% 0.19/0.43  cnf(c_0_94, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_90]), c_0_64])).
% 0.19/0.43  cnf(c_0_95, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_91]), c_0_77]), c_0_68])])).
% 0.19/0.43  cnf(c_0_96, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|esk9_0=k1_xboole_0|~r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 0.19/0.43  cnf(c_0_97, negated_conjecture, (k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0)=k2_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0)))|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_47])).
% 0.19/0.43  cnf(c_0_98, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk10_0))),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_95]), c_0_64])).
% 0.19/0.43  cnf(c_0_99, negated_conjecture, (esk9_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])).
% 0.19/0.43  fof(c_0_100, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.43  cnf(c_0_101, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_99]), c_0_50]), c_0_68])])).
% 0.19/0.43  fof(c_0_102, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k3_xboole_0(X14,X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.43  cnf(c_0_103, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.19/0.43  cnf(c_0_104, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_105, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_101]), c_0_77]), c_0_68])])).
% 0.19/0.43  cnf(c_0_106, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  cnf(c_0_107, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.19/0.43  cnf(c_0_108, negated_conjecture, (r1_tarski(esk9_0,esk5_0)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.19/0.43  cnf(c_0_109, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_105]), c_0_86]), c_0_68])])).
% 0.19/0.43  cnf(c_0_110, plain, (k4_zfmisc_1(k1_xboole_0,X1,X2,X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_106])).
% 0.19/0.43  cnf(c_0_111, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_112, negated_conjecture, (k3_xboole_0(esk9_0,esk5_0)=esk9_0), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.19/0.43  cnf(c_0_113, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_109]), c_0_110]), c_0_68])])).
% 0.19/0.43  cnf(c_0_114, negated_conjecture, (r1_tarski(esk8_0,esk4_0)), inference(spm,[status(thm)],[c_0_103, c_0_111])).
% 0.19/0.43  cnf(c_0_115, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_51])).
% 0.19/0.43  cnf(c_0_116, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_117, negated_conjecture, (k3_xboole_0(esk8_0,esk4_0)=esk8_0), inference(spm,[status(thm)],[c_0_107, c_0_114])).
% 0.19/0.43  cnf(c_0_118, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_115]), c_0_50]), c_0_68])])).
% 0.19/0.43  cnf(c_0_119, negated_conjecture, (r1_tarski(esk7_0,esk3_0)), inference(spm,[status(thm)],[c_0_103, c_0_116])).
% 0.19/0.43  cnf(c_0_120, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_51])).
% 0.19/0.43  cnf(c_0_121, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_122, negated_conjecture, (k3_xboole_0(esk7_0,esk3_0)=esk7_0), inference(spm,[status(thm)],[c_0_107, c_0_119])).
% 0.19/0.43  cnf(c_0_123, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_120]), c_0_77]), c_0_68])])).
% 0.19/0.43  cnf(c_0_124, negated_conjecture, (r1_tarski(esk6_0,esk2_0)), inference(spm,[status(thm)],[c_0_103, c_0_121])).
% 0.19/0.43  cnf(c_0_125, negated_conjecture, (esk2_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_51])).
% 0.19/0.43  cnf(c_0_126, negated_conjecture, (k3_xboole_0(esk6_0,esk2_0)=esk6_0), inference(spm,[status(thm)],[c_0_107, c_0_124])).
% 0.19/0.43  cnf(c_0_127, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_125]), c_0_86]), c_0_68])])).
% 0.19/0.43  cnf(c_0_128, negated_conjecture, (esk6_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_127]), c_0_51])).
% 0.19/0.43  cnf(c_0_129, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_128]), c_0_110]), c_0_51]), c_0_52]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 130
% 0.19/0.43  # Proof object clause steps            : 97
% 0.19/0.43  # Proof object formula steps           : 33
% 0.19/0.43  # Proof object conjectures             : 67
% 0.19/0.43  # Proof object clause conjectures      : 64
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 30
% 0.19/0.43  # Proof object initial formulas used   : 16
% 0.19/0.43  # Proof object generating inferences   : 59
% 0.19/0.43  # Proof object simplifying inferences  : 64
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 16
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 37
% 0.19/0.43  # Removed in clause preprocessing      : 0
% 0.19/0.43  # Initial clauses in saturation        : 37
% 0.19/0.43  # Processed clauses                    : 661
% 0.19/0.43  # ...of these trivial                  : 75
% 0.19/0.43  # ...subsumed                          : 197
% 0.19/0.43  # ...remaining for further processing  : 389
% 0.19/0.43  # Other redundant clauses eliminated   : 5
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 41
% 0.19/0.43  # Backward-rewritten                   : 115
% 0.19/0.43  # Generated clauses                    : 2211
% 0.19/0.43  # ...of the previous two non-trivial   : 1844
% 0.19/0.43  # Contextual simplify-reflections      : 39
% 0.19/0.43  # Paramodulations                      : 2206
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 5
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 191
% 0.19/0.43  #    Positive orientable unit clauses  : 38
% 0.19/0.43  #    Positive unorientable unit clauses: 0
% 0.19/0.43  #    Negative unit clauses             : 1
% 0.19/0.43  #    Non-unit-clauses                  : 152
% 0.19/0.43  # Current number of unprocessed clauses: 1086
% 0.19/0.43  # ...number of literals in the above   : 3978
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 193
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 5360
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 2864
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 272
% 0.19/0.43  # Unit Clause-clause subsumption calls : 1284
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 123
% 0.19/0.43  # BW rewrite match successes           : 8
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 32782
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.081 s
% 0.19/0.43  # System time              : 0.005 s
% 0.19/0.43  # Total time               : 0.086 s
% 0.19/0.43  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
