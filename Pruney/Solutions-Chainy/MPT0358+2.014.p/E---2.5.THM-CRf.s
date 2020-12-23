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
% DateTime   : Thu Dec  3 10:45:52 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 419 expanded)
%              Number of clauses        :   56 ( 192 expanded)
%              Number of leaves         :   16 ( 103 expanded)
%              Depth                    :   15
%              Number of atoms          :  201 (1232 expanded)
%              Number of equality atoms :   49 ( 299 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

fof(c_0_17,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( ( ~ r2_hidden(X41,X40)
        | r1_tarski(X41,X39)
        | X40 != k1_zfmisc_1(X39) )
      & ( ~ r1_tarski(X42,X39)
        | r2_hidden(X42,X40)
        | X40 != k1_zfmisc_1(X39) )
      & ( ~ r2_hidden(esk5_2(X43,X44),X44)
        | ~ r1_tarski(esk5_2(X43,X44),X43)
        | X44 = k1_zfmisc_1(X43) )
      & ( r2_hidden(esk5_2(X43,X44),X44)
        | r1_tarski(esk5_2(X43,X44),X43)
        | X44 = k1_zfmisc_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_18,plain,(
    ! [X46,X47] :
      ( ( ~ m1_subset_1(X47,X46)
        | r2_hidden(X47,X46)
        | v1_xboole_0(X46) )
      & ( ~ r2_hidden(X47,X46)
        | m1_subset_1(X47,X46)
        | v1_xboole_0(X46) )
      & ( ~ m1_subset_1(X47,X46)
        | v1_xboole_0(X47)
        | ~ v1_xboole_0(X46) )
      & ( ~ v1_xboole_0(X47)
        | m1_subset_1(X47,X46)
        | ~ v1_xboole_0(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_19,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))
    & ( ~ r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))
      | esk7_0 != k1_subset_1(esk6_0) )
    & ( r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))
      | esk7_0 = k1_subset_1(esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X53] : ~ v1_xboole_0(k1_zfmisc_1(X53)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X34,X35] :
      ( ~ r1_tarski(X34,X35)
      | k3_xboole_0(X34,X35) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_28,plain,(
    ! [X22,X23] :
      ( ( ~ r1_xboole_0(X22,X23)
        | k3_xboole_0(X22,X23) = k1_xboole_0 )
      & ( k3_xboole_0(X22,X23) != k1_xboole_0
        | r1_xboole_0(X22,X23) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( k3_xboole_0(esk7_0,esk6_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_33,plain,(
    ! [X30] :
      ( X30 = k1_xboole_0
      | r2_hidden(esk4_1(X30),X30) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_34,plain,(
    ! [X48] : k1_subset_1(X48) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_35,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_36,plain,(
    ! [X24,X25,X27,X28,X29] :
      ( ( r2_hidden(esk3_2(X24,X25),X24)
        | r1_xboole_0(X24,X25) )
      & ( r2_hidden(esk3_2(X24,X25),X25)
        | r1_xboole_0(X24,X25) )
      & ( ~ r2_hidden(X29,X27)
        | ~ r2_hidden(X29,X28)
        | ~ r1_xboole_0(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(esk7_0,esk6_0)
    | esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))
    | esk7_0 = k1_subset_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_41,plain,(
    ! [X51,X52] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(X51))
      | m1_subset_1(k3_subset_1(X51,X52),k1_zfmisc_1(X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))
    | esk7_0 != k1_subset_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk6_0)
    | r2_hidden(esk4_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | ~ r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_1(esk7_0),esk7_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk6_0)
    | r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_23])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_54,plain,(
    ! [X36,X37,X38] :
      ( ~ r1_tarski(X36,X37)
      | r1_xboole_0(X36,k4_xboole_0(X38,X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_55,plain,(
    ! [X32,X33] : k4_xboole_0(X32,X33) = k5_xboole_0(X32,k3_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk4_1(esk7_0),esk7_0)
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(esk6_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_38])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk4_1(esk7_0),esk7_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_51])).

fof(c_0_60,plain,(
    ! [X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(X49))
      | k3_subset_1(X49,X50) = k4_xboole_0(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_52]),c_0_24])).

fof(c_0_62,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_63,plain,(
    ! [X54,X55] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(X54))
      | k3_subset_1(X54,k3_subset_1(X54,X55)) = X55 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk4_1(esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_46]),c_0_59])).

cnf(c_0_69,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk6_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_61])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_74,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_57])).

cnf(c_0_75,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_46]),c_0_68])).

cnf(c_0_77,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_66])).

cnf(c_0_78,negated_conjecture,
    ( k3_xboole_0(esk6_0,k3_subset_1(esk6_0,esk7_0)) = k3_subset_1(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_70]),c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( k3_subset_1(esk6_0,k3_subset_1(esk6_0,esk7_0)) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_23])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_64])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(esk7_0,k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(esk6_0,esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_subset_1(esk6_0,esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_52]),c_0_78]),c_0_79])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_80])).

cnf(c_0_84,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_85,negated_conjecture,
    ( r1_xboole_0(esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_78]),c_0_82])).

cnf(c_0_86,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_76])])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_87]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:14:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.56/2.81  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 2.56/2.81  # and selection function SelectCQIArEqFirst.
% 2.56/2.81  #
% 2.56/2.81  # Preprocessing time       : 0.032 s
% 2.56/2.81  # Presaturation interreduction done
% 2.56/2.81  
% 2.56/2.81  # Proof found!
% 2.56/2.81  # SZS status Theorem
% 2.56/2.81  # SZS output start CNFRefutation
% 2.56/2.81  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.56/2.81  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.56/2.81  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.56/2.81  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.56/2.81  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.56/2.81  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.56/2.81  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.56/2.81  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.56/2.81  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.56/2.81  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.56/2.81  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.56/2.81  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.56/2.81  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.56/2.81  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.56/2.81  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.56/2.81  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.56/2.81  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 2.56/2.81  fof(c_0_17, plain, ![X39, X40, X41, X42, X43, X44]:(((~r2_hidden(X41,X40)|r1_tarski(X41,X39)|X40!=k1_zfmisc_1(X39))&(~r1_tarski(X42,X39)|r2_hidden(X42,X40)|X40!=k1_zfmisc_1(X39)))&((~r2_hidden(esk5_2(X43,X44),X44)|~r1_tarski(esk5_2(X43,X44),X43)|X44=k1_zfmisc_1(X43))&(r2_hidden(esk5_2(X43,X44),X44)|r1_tarski(esk5_2(X43,X44),X43)|X44=k1_zfmisc_1(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 2.56/2.81  fof(c_0_18, plain, ![X46, X47]:(((~m1_subset_1(X47,X46)|r2_hidden(X47,X46)|v1_xboole_0(X46))&(~r2_hidden(X47,X46)|m1_subset_1(X47,X46)|v1_xboole_0(X46)))&((~m1_subset_1(X47,X46)|v1_xboole_0(X47)|~v1_xboole_0(X46))&(~v1_xboole_0(X47)|m1_subset_1(X47,X46)|~v1_xboole_0(X46)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 2.56/2.81  fof(c_0_19, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))&((~r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))|esk7_0!=k1_subset_1(esk6_0))&(r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))|esk7_0=k1_subset_1(esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 2.56/2.81  fof(c_0_20, plain, ![X53]:~v1_xboole_0(k1_zfmisc_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 2.56/2.81  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.56/2.81  cnf(c_0_22, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.56/2.81  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.56/2.81  cnf(c_0_24, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.56/2.81  fof(c_0_25, plain, ![X34, X35]:(~r1_tarski(X34,X35)|k3_xboole_0(X34,X35)=X34), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 2.56/2.81  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_21])).
% 2.56/2.81  cnf(c_0_27, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 2.56/2.81  fof(c_0_28, plain, ![X22, X23]:((~r1_xboole_0(X22,X23)|k3_xboole_0(X22,X23)=k1_xboole_0)&(k3_xboole_0(X22,X23)!=k1_xboole_0|r1_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 2.56/2.81  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.56/2.81  cnf(c_0_30, negated_conjecture, (r1_tarski(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 2.56/2.81  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.56/2.81  cnf(c_0_32, negated_conjecture, (k3_xboole_0(esk7_0,esk6_0)=esk7_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 2.56/2.81  fof(c_0_33, plain, ![X30]:(X30=k1_xboole_0|r2_hidden(esk4_1(X30),X30)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 2.56/2.81  fof(c_0_34, plain, ![X48]:k1_subset_1(X48)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 2.56/2.81  fof(c_0_35, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.56/2.81  fof(c_0_36, plain, ![X24, X25, X27, X28, X29]:(((r2_hidden(esk3_2(X24,X25),X24)|r1_xboole_0(X24,X25))&(r2_hidden(esk3_2(X24,X25),X25)|r1_xboole_0(X24,X25)))&(~r2_hidden(X29,X27)|~r2_hidden(X29,X28)|~r1_xboole_0(X27,X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 2.56/2.81  cnf(c_0_37, negated_conjecture, (r1_xboole_0(esk7_0,esk6_0)|esk7_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 2.56/2.81  cnf(c_0_38, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.56/2.81  cnf(c_0_39, negated_conjecture, (r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))|esk7_0=k1_subset_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.56/2.81  cnf(c_0_40, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.56/2.81  fof(c_0_41, plain, ![X51, X52]:(~m1_subset_1(X52,k1_zfmisc_1(X51))|m1_subset_1(k3_subset_1(X51,X52),k1_zfmisc_1(X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 2.56/2.81  cnf(c_0_42, negated_conjecture, (~r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))|esk7_0!=k1_subset_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.56/2.81  cnf(c_0_43, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.56/2.81  cnf(c_0_44, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.56/2.81  cnf(c_0_45, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk6_0)|r2_hidden(esk4_1(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.56/2.81  cnf(c_0_46, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 2.56/2.81  cnf(c_0_47, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.56/2.81  cnf(c_0_48, negated_conjecture, (esk7_0!=k1_xboole_0|~r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))), inference(rw,[status(thm)],[c_0_42, c_0_40])).
% 2.56/2.81  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_43, c_0_30])).
% 2.56/2.81  cnf(c_0_50, negated_conjecture, (r2_hidden(esk4_1(esk7_0),esk7_0)|~r2_hidden(X1,esk6_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 2.56/2.81  cnf(c_0_51, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk6_0)|r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_37, c_0_46])).
% 2.56/2.81  cnf(c_0_52, negated_conjecture, (m1_subset_1(k3_subset_1(esk6_0,esk7_0),k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_47, c_0_23])).
% 2.56/2.81  cnf(c_0_53, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.56/2.81  fof(c_0_54, plain, ![X36, X37, X38]:(~r1_tarski(X36,X37)|r1_xboole_0(X36,k4_xboole_0(X38,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 2.56/2.81  fof(c_0_55, plain, ![X32, X33]:k4_xboole_0(X32,X33)=k5_xboole_0(X32,k3_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.56/2.81  cnf(c_0_56, negated_conjecture, (r2_hidden(esk4_1(esk7_0),esk7_0)|~r1_tarski(k1_xboole_0,k3_subset_1(esk6_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_48, c_0_38])).
% 2.56/2.81  cnf(c_0_57, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.56/2.81  cnf(c_0_58, negated_conjecture, (r2_hidden(esk4_1(esk7_0),esk7_0)|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_38]), c_0_50])).
% 2.56/2.81  cnf(c_0_59, negated_conjecture, (r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))|~r2_hidden(X1,esk6_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_51])).
% 2.56/2.81  fof(c_0_60, plain, ![X49, X50]:(~m1_subset_1(X50,k1_zfmisc_1(X49))|k3_subset_1(X49,X50)=k4_xboole_0(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 2.56/2.81  cnf(c_0_61, negated_conjecture, (r2_hidden(k3_subset_1(esk6_0,esk7_0),k1_zfmisc_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_52]), c_0_24])).
% 2.56/2.81  fof(c_0_62, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.56/2.81  fof(c_0_63, plain, ![X54, X55]:(~m1_subset_1(X55,k1_zfmisc_1(X54))|k3_subset_1(X54,k3_subset_1(X54,X55))=X55), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 2.56/2.81  cnf(c_0_64, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_53])).
% 2.56/2.81  cnf(c_0_65, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 2.56/2.81  cnf(c_0_66, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 2.56/2.81  cnf(c_0_67, negated_conjecture, (r2_hidden(esk4_1(esk7_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 2.56/2.81  cnf(c_0_68, negated_conjecture, (r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_46]), c_0_59])).
% 2.56/2.81  cnf(c_0_69, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 2.56/2.81  cnf(c_0_70, negated_conjecture, (r1_tarski(k3_subset_1(esk6_0,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_61])).
% 2.56/2.81  cnf(c_0_71, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 2.56/2.81  cnf(c_0_72, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.56/2.81  cnf(c_0_73, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.56/2.81  cnf(c_0_74, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_64, c_0_57])).
% 2.56/2.81  cnf(c_0_75, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 2.56/2.81  cnf(c_0_76, negated_conjecture, (r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_46]), c_0_68])).
% 2.56/2.81  cnf(c_0_77, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_69, c_0_66])).
% 2.56/2.81  cnf(c_0_78, negated_conjecture, (k3_xboole_0(esk6_0,k3_subset_1(esk6_0,esk7_0))=k3_subset_1(esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_70]), c_0_71])).
% 2.56/2.81  cnf(c_0_79, negated_conjecture, (k3_subset_1(esk6_0,k3_subset_1(esk6_0,esk7_0))=esk7_0), inference(spm,[status(thm)],[c_0_72, c_0_23])).
% 2.56/2.81  cnf(c_0_80, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_64])).
% 2.56/2.81  cnf(c_0_81, negated_conjecture, (r1_xboole_0(esk7_0,k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(esk6_0,esk7_0))))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 2.56/2.81  cnf(c_0_82, negated_conjecture, (k5_xboole_0(esk6_0,k3_subset_1(esk6_0,esk7_0))=esk7_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_52]), c_0_78]), c_0_79])).
% 2.56/2.81  cnf(c_0_83, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_26, c_0_80])).
% 2.56/2.81  cnf(c_0_84, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.56/2.81  cnf(c_0_85, negated_conjecture, (r1_xboole_0(esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_78]), c_0_82])).
% 2.56/2.81  cnf(c_0_86, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_29, c_0_83])).
% 2.56/2.81  cnf(c_0_87, negated_conjecture, (esk7_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_76])])).
% 2.56/2.81  cnf(c_0_88, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_87]), ['proof']).
% 2.56/2.81  # SZS output end CNFRefutation
% 2.56/2.81  # Proof object total steps             : 89
% 2.56/2.81  # Proof object clause steps            : 56
% 2.56/2.81  # Proof object formula steps           : 33
% 2.56/2.81  # Proof object conjectures             : 32
% 2.56/2.81  # Proof object clause conjectures      : 29
% 2.56/2.81  # Proof object formula conjectures     : 3
% 2.56/2.81  # Proof object initial clauses used    : 22
% 2.56/2.81  # Proof object initial formulas used   : 16
% 2.56/2.81  # Proof object generating inferences   : 27
% 2.56/2.81  # Proof object simplifying inferences  : 21
% 2.56/2.81  # Training examples: 0 positive, 0 negative
% 2.56/2.81  # Parsed axioms                        : 17
% 2.56/2.81  # Removed by relevancy pruning/SinE    : 0
% 2.56/2.81  # Initial clauses                      : 35
% 2.56/2.81  # Removed in clause preprocessing      : 2
% 2.56/2.81  # Initial clauses in saturation        : 33
% 2.56/2.81  # Processed clauses                    : 9819
% 2.56/2.81  # ...of these trivial                  : 1032
% 2.56/2.81  # ...subsumed                          : 6224
% 2.56/2.81  # ...remaining for further processing  : 2563
% 2.56/2.81  # Other redundant clauses eliminated   : 971
% 2.56/2.81  # Clauses deleted for lack of memory   : 0
% 2.56/2.81  # Backward-subsumed                    : 78
% 2.56/2.81  # Backward-rewritten                   : 596
% 2.56/2.81  # Generated clauses                    : 393384
% 2.56/2.81  # ...of the previous two non-trivial   : 303211
% 2.56/2.81  # Contextual simplify-reflections      : 16
% 2.56/2.81  # Paramodulations                      : 392376
% 2.56/2.81  # Factorizations                       : 30
% 2.56/2.81  # Equation resolutions                 : 971
% 2.56/2.81  # Propositional unsat checks           : 0
% 2.56/2.81  #    Propositional check models        : 0
% 2.56/2.81  #    Propositional check unsatisfiable : 0
% 2.56/2.81  #    Propositional clauses             : 0
% 2.56/2.81  #    Propositional clauses after purity: 0
% 2.56/2.81  #    Propositional unsat core size     : 0
% 2.56/2.81  #    Propositional preprocessing time  : 0.000
% 2.56/2.81  #    Propositional encoding time       : 0.000
% 2.56/2.81  #    Propositional solver time         : 0.000
% 2.56/2.81  #    Success case prop preproc time    : 0.000
% 2.56/2.81  #    Success case prop encoding time   : 0.000
% 2.56/2.81  #    Success case prop solver time     : 0.000
% 2.56/2.81  # Current number of processed clauses  : 1844
% 2.56/2.81  #    Positive orientable unit clauses  : 417
% 2.56/2.81  #    Positive unorientable unit clauses: 1
% 2.56/2.81  #    Negative unit clauses             : 259
% 2.56/2.81  #    Non-unit-clauses                  : 1167
% 2.56/2.81  # Current number of unprocessed clauses: 288494
% 2.56/2.81  # ...number of literals in the above   : 1220739
% 2.56/2.81  # Current number of archived formulas  : 0
% 2.56/2.81  # Current number of archived clauses   : 716
% 2.56/2.81  # Clause-clause subsumption calls (NU) : 326451
% 2.56/2.81  # Rec. Clause-clause subsumption calls : 208840
% 2.56/2.81  # Non-unit clause-clause subsumptions  : 3168
% 2.56/2.81  # Unit Clause-clause subsumption calls : 49293
% 2.56/2.81  # Rewrite failures with RHS unbound    : 0
% 2.56/2.81  # BW rewrite match attempts            : 1227
% 2.56/2.81  # BW rewrite match successes           : 133
% 2.56/2.81  # Condensation attempts                : 0
% 2.56/2.81  # Condensation successes               : 0
% 2.56/2.81  # Termbank termtop insertions          : 6367516
% 2.56/2.82  
% 2.56/2.82  # -------------------------------------------------
% 2.56/2.82  # User time                : 2.379 s
% 2.56/2.82  # System time              : 0.102 s
% 2.56/2.82  # Total time               : 2.480 s
% 2.56/2.82  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
