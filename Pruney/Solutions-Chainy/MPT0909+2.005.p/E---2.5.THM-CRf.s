%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 285 expanded)
%              Number of clauses        :   48 ( 119 expanded)
%              Number of leaves         :   13 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  228 (1340 expanded)
%              Number of equality atoms :  109 ( 711 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X6 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k5_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(t50_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X6 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k5_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_mcart_1])).

fof(c_0_14,plain,(
    ! [X29,X30,X31] :
      ( ( r2_hidden(k1_mcart_1(X29),X30)
        | ~ r2_hidden(X29,k2_zfmisc_1(X30,X31)) )
      & ( r2_hidden(k2_mcart_1(X29),X31)
        | ~ r2_hidden(X29,k2_zfmisc_1(X30,X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X16,X15)
        | r2_hidden(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ r2_hidden(X16,X15)
        | m1_subset_1(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ m1_subset_1(X16,X15)
        | v1_xboole_0(X16)
        | ~ v1_xboole_0(X15) )
      & ( ~ v1_xboole_0(X16)
        | m1_subset_1(X16,X15)
        | ~ v1_xboole_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_16,negated_conjecture,(
    ! [X46,X47,X48] :
      ( m1_subset_1(esk6_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))
      & ( ~ m1_subset_1(X46,esk2_0)
        | ~ m1_subset_1(X47,esk3_0)
        | ~ m1_subset_1(X48,esk4_0)
        | esk6_0 != k3_mcart_1(X46,X47,X48)
        | esk5_0 = X46 )
      & esk2_0 != k1_xboole_0
      & esk3_0 != k1_xboole_0
      & esk4_0 != k1_xboole_0
      & esk5_0 != k5_mcart_1(esk2_0,esk3_0,esk4_0,esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_17,plain,(
    ! [X22,X23,X24] : k3_zfmisc_1(X22,X23,X24) = k2_zfmisc_1(k2_zfmisc_1(X22,X23),X24) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | X13 = X14
      | ~ v1_xboole_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_19,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk6_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X34,X35,X36] :
      ( ( X34 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0
        | k3_zfmisc_1(X34,X35,X36) != k1_xboole_0 )
      & ( X34 != k1_xboole_0
        | k3_zfmisc_1(X34,X35,X36) = k1_xboole_0 )
      & ( X35 != k1_xboole_0
        | k3_zfmisc_1(X34,X35,X36) = k1_xboole_0 )
      & ( X36 != k1_xboole_0
        | k3_zfmisc_1(X34,X35,X36) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_26,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | v1_xboole_0(k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(esk2_0,esk3_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_31,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r2_hidden(X32,X33)
      | X32 = k4_tarski(k1_mcart_1(X32),k2_mcart_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_32,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_33,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_38,plain,(
    ! [X25,X26,X27,X28] :
      ( ~ m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))
      | m1_subset_1(k7_mcart_1(X25,X26,X27,X28),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

fof(c_0_39,plain,(
    ! [X37,X38,X39,X40] :
      ( ( k5_mcart_1(X37,X38,X39,X40) = k1_mcart_1(k1_mcart_1(X40))
        | ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 )
      & ( k6_mcart_1(X37,X38,X39,X40) = k2_mcart_1(k1_mcart_1(X40))
        | ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 )
      & ( k7_mcart_1(X37,X38,X39,X40) = k2_mcart_1(X40)
        | ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_40,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X17,X18] : v1_relat_1(k2_zfmisc_1(X17,X18)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_42,plain,(
    ! [X19,X20,X21] : k3_mcart_1(X19,X20,X21) = k4_tarski(k4_tarski(X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_47,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | v1_xboole_0(X2)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_20])).

cnf(c_0_50,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( esk5_0 = X1
    | ~ m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X2,esk3_0)
    | ~ m1_subset_1(X3,esk4_0)
    | esk6_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_52,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk6_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk6_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_46])).

cnf(c_0_56,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_22])).

cnf(c_0_57,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk6_0),k2_mcart_1(esk6_0)) = esk6_0
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_50])])).

cnf(c_0_59,negated_conjecture,
    ( esk5_0 = X1
    | esk6_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk3_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk6_0)),k2_mcart_1(k1_mcart_1(esk6_0))) = k1_mcart_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_46]),c_0_50])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(esk6_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(esk6_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_55])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | m1_subset_1(k2_mcart_1(X4),X3)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk6_0),k2_mcart_1(esk6_0)) = esk6_0
    | k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( esk5_0 = k1_mcart_1(k1_mcart_1(esk6_0))
    | k4_tarski(k1_mcart_1(esk6_0),X1) != esk6_0
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk6_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_27]),c_0_37]),c_0_36]),c_0_35])).

cnf(c_0_67,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk6_0),k2_mcart_1(esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_64]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_68,negated_conjecture,
    ( esk5_0 != k5_mcart_1(esk2_0,esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 = k1_mcart_1(k1_mcart_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_70,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_71,negated_conjecture,
    ( k5_mcart_1(esk2_0,esk3_0,esk4_0,esk6_0) != k1_mcart_1(k1_mcart_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_22])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_27])]),c_0_35]),c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t69_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 0.19/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.19/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.38  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.19/0.38  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.19/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.38  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 0.19/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.38  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 0.19/0.38  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.19/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.38  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.19/0.38  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t69_mcart_1])).
% 0.19/0.38  fof(c_0_14, plain, ![X29, X30, X31]:((r2_hidden(k1_mcart_1(X29),X30)|~r2_hidden(X29,k2_zfmisc_1(X30,X31)))&(r2_hidden(k2_mcart_1(X29),X31)|~r2_hidden(X29,k2_zfmisc_1(X30,X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.19/0.38  fof(c_0_15, plain, ![X15, X16]:(((~m1_subset_1(X16,X15)|r2_hidden(X16,X15)|v1_xboole_0(X15))&(~r2_hidden(X16,X15)|m1_subset_1(X16,X15)|v1_xboole_0(X15)))&((~m1_subset_1(X16,X15)|v1_xboole_0(X16)|~v1_xboole_0(X15))&(~v1_xboole_0(X16)|m1_subset_1(X16,X15)|~v1_xboole_0(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.38  fof(c_0_16, negated_conjecture, ![X46, X47, X48]:(m1_subset_1(esk6_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))&((~m1_subset_1(X46,esk2_0)|(~m1_subset_1(X47,esk3_0)|(~m1_subset_1(X48,esk4_0)|(esk6_0!=k3_mcart_1(X46,X47,X48)|esk5_0=X46))))&(((esk2_0!=k1_xboole_0&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&esk5_0!=k5_mcart_1(esk2_0,esk3_0,esk4_0,esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.19/0.38  fof(c_0_17, plain, ![X22, X23, X24]:k3_zfmisc_1(X22,X23,X24)=k2_zfmisc_1(k2_zfmisc_1(X22,X23),X24), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.38  fof(c_0_18, plain, ![X13, X14]:(~v1_xboole_0(X13)|X13=X14|~v1_xboole_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.19/0.38  cnf(c_0_19, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_20, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk6_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_22, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  fof(c_0_23, plain, ![X34, X35, X36]:((X34=k1_xboole_0|X35=k1_xboole_0|X36=k1_xboole_0|k3_zfmisc_1(X34,X35,X36)!=k1_xboole_0)&(((X34!=k1_xboole_0|k3_zfmisc_1(X34,X35,X36)=k1_xboole_0)&(X35!=k1_xboole_0|k3_zfmisc_1(X34,X35,X36)=k1_xboole_0))&(X36!=k1_xboole_0|k3_zfmisc_1(X34,X35,X36)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.19/0.38  cnf(c_0_24, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_25, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.38  cnf(c_0_26, plain, (r2_hidden(k1_mcart_1(X1),X2)|v1_xboole_0(k2_zfmisc_1(X2,X3))|~m1_subset_1(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.38  cnf(c_0_28, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_29, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(esk2_0,esk3_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.38  fof(c_0_31, plain, ![X32, X33]:(~v1_relat_1(X33)|(~r2_hidden(X32,X33)|X32=k4_tarski(k1_mcart_1(X32),k2_mcart_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 0.19/0.38  fof(c_0_32, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.38  cnf(c_0_33, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_28, c_0_22])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)=k1_xboole_0|r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_38, plain, ![X25, X26, X27, X28]:(~m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))|m1_subset_1(k7_mcart_1(X25,X26,X27,X28),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 0.19/0.38  fof(c_0_39, plain, ![X37, X38, X39, X40]:(((k5_mcart_1(X37,X38,X39,X40)=k1_mcart_1(k1_mcart_1(X40))|~m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))|(X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0))&(k6_mcart_1(X37,X38,X39,X40)=k2_mcart_1(k1_mcart_1(X40))|~m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))|(X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0)))&(k7_mcart_1(X37,X38,X39,X40)=k2_mcart_1(X40)|~m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))|(X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.19/0.38  cnf(c_0_40, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  fof(c_0_41, plain, ![X17, X18]:v1_relat_1(k2_zfmisc_1(X17,X18)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.38  fof(c_0_42, plain, ![X19, X20, X21]:k3_mcart_1(X19,X20,X21)=k4_tarski(k4_tarski(X19,X20),X21), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.19/0.38  cnf(c_0_43, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_44, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_45, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.19/0.38  cnf(c_0_47, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_48, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_49, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|v1_xboole_0(X2)|~v1_relat_1(X2)|~m1_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_20])).
% 0.19/0.38  cnf(c_0_50, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (esk5_0=X1|~m1_subset_1(X1,esk2_0)|~m1_subset_1(X2,esk3_0)|~m1_subset_1(X3,esk4_0)|esk6_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_52, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_53, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk6_0)),esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk6_0)),esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_46])).
% 0.19/0.38  cnf(c_0_56, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_47, c_0_22])).
% 0.19/0.38  cnf(c_0_57, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_48, c_0_22])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (k4_tarski(k1_mcart_1(esk6_0),k2_mcart_1(esk6_0))=esk6_0|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_50])])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (esk5_0=X1|esk6_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk3_0)|~m1_subset_1(X1,esk2_0)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk6_0)),k2_mcart_1(k1_mcart_1(esk6_0)))=k1_mcart_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_46]), c_0_50])])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (m1_subset_1(k2_mcart_1(k1_mcart_1(esk6_0)),esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (m1_subset_1(k1_mcart_1(k1_mcart_1(esk6_0)),esk2_0)), inference(spm,[status(thm)],[c_0_53, c_0_55])).
% 0.19/0.38  cnf(c_0_63, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|m1_subset_1(k2_mcart_1(X4),X3)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (k4_tarski(k1_mcart_1(esk6_0),k2_mcart_1(esk6_0))=esk6_0|k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_58])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (esk5_0=k1_mcart_1(k1_mcart_1(esk6_0))|k4_tarski(k1_mcart_1(esk6_0),X1)!=esk6_0|~m1_subset_1(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62])])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (m1_subset_1(k2_mcart_1(esk6_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_27]), c_0_37]), c_0_36]), c_0_35])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (k4_tarski(k1_mcart_1(esk6_0),k2_mcart_1(esk6_0))=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_64]), c_0_35]), c_0_36]), c_0_37])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (esk5_0!=k5_mcart_1(esk2_0,esk3_0,esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (esk5_0=k1_mcart_1(k1_mcart_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.19/0.38  cnf(c_0_70, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (k5_mcart_1(esk2_0,esk3_0,esk4_0,esk6_0)!=k1_mcart_1(k1_mcart_1(esk6_0))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.38  cnf(c_0_72, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_70, c_0_22])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_27])]), c_0_35]), c_0_36]), c_0_37]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 74
% 0.19/0.38  # Proof object clause steps            : 48
% 0.19/0.38  # Proof object formula steps           : 26
% 0.19/0.38  # Proof object conjectures             : 27
% 0.19/0.38  # Proof object clause conjectures      : 24
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 21
% 0.19/0.38  # Proof object initial formulas used   : 13
% 0.19/0.38  # Proof object generating inferences   : 19
% 0.19/0.38  # Proof object simplifying inferences  : 31
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 13
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 28
% 0.19/0.38  # Removed in clause preprocessing      : 2
% 0.19/0.38  # Initial clauses in saturation        : 26
% 0.19/0.38  # Processed clauses                    : 208
% 0.19/0.38  # ...of these trivial                  : 12
% 0.19/0.38  # ...subsumed                          : 70
% 0.19/0.38  # ...remaining for further processing  : 126
% 0.19/0.38  # Other redundant clauses eliminated   : 5
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 4
% 0.19/0.38  # Backward-rewritten                   : 17
% 0.19/0.38  # Generated clauses                    : 516
% 0.19/0.38  # ...of the previous two non-trivial   : 380
% 0.19/0.38  # Contextual simplify-reflections      : 2
% 0.19/0.38  # Paramodulations                      : 491
% 0.19/0.38  # Factorizations                       : 15
% 0.19/0.38  # Equation resolutions                 : 10
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 79
% 0.19/0.38  #    Positive orientable unit clauses  : 16
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 8
% 0.19/0.38  #    Non-unit-clauses                  : 55
% 0.19/0.38  # Current number of unprocessed clauses: 82
% 0.19/0.38  # ...number of literals in the above   : 387
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 49
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 480
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 175
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 28
% 0.19/0.38  # Unit Clause-clause subsumption calls : 44
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 6
% 0.19/0.38  # BW rewrite match successes           : 6
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 7160
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.040 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.043 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
