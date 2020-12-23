%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:28 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 438 expanded)
%              Number of clauses        :   59 ( 182 expanded)
%              Number of leaves         :   16 ( 109 expanded)
%              Depth                    :   13
%              Number of atoms          :  280 (2028 expanded)
%              Number of equality atoms :  166 (1248 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t81_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))
     => ( ! [X7] :
            ( m1_subset_1(X7,X1)
           => ! [X8] :
                ( m1_subset_1(X8,X2)
               => ! [X9] :
                    ( m1_subset_1(X9,X3)
                   => ! [X10] :
                        ( m1_subset_1(X10,X4)
                       => ( X6 = k4_mcart_1(X7,X8,X9,X10)
                         => X5 = X9 ) ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | X5 = k10_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(dt_k9_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(dt_k8_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(dt_k10_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(dt_k11_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))
       => ( ! [X7] :
              ( m1_subset_1(X7,X1)
             => ! [X8] :
                  ( m1_subset_1(X8,X2)
                 => ! [X9] :
                      ( m1_subset_1(X9,X3)
                     => ! [X10] :
                          ( m1_subset_1(X10,X4)
                         => ( X6 = k4_mcart_1(X7,X8,X9,X10)
                           => X5 = X9 ) ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k1_xboole_0
            | X5 = k10_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t81_mcart_1])).

fof(c_0_17,plain,(
    ! [X26,X27,X28,X29] : k4_zfmisc_1(X26,X27,X28,X29) = k2_zfmisc_1(k3_zfmisc_1(X26,X27,X28),X29) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X19,X20,X21] : k3_zfmisc_1(X19,X20,X21) = k2_zfmisc_1(k2_zfmisc_1(X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_19,negated_conjecture,(
    ! [X70,X71,X72,X73] :
      ( m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
      & ( ~ m1_subset_1(X70,esk1_0)
        | ~ m1_subset_1(X71,esk2_0)
        | ~ m1_subset_1(X72,esk3_0)
        | ~ m1_subset_1(X73,esk4_0)
        | esk6_0 != k4_mcart_1(X70,X71,X72,X73)
        | esk5_0 = X72 )
      & esk1_0 != k1_xboole_0
      & esk2_0 != k1_xboole_0
      & esk3_0 != k1_xboole_0
      & esk4_0 != k1_xboole_0
      & esk5_0 != k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])).

cnf(c_0_20,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,X13)
      | v1_xboole_0(X13)
      | r2_hidden(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_25,plain,(
    ! [X11] :
      ( ~ v1_xboole_0(X11)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X50,X51,X52] :
      ( ( r2_hidden(k1_mcart_1(X50),X51)
        | ~ r2_hidden(X50,k2_zfmisc_1(X51,X52)) )
      & ( r2_hidden(k2_mcart_1(X50),X52)
        | ~ r2_hidden(X50,k2_zfmisc_1(X51,X52)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_31,plain,(
    ! [X59,X60,X61,X62,X63] :
      ( ( k8_mcart_1(X59,X60,X61,X62,X63) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X63)))
        | ~ m1_subset_1(X63,k4_zfmisc_1(X59,X60,X61,X62))
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0
        | X62 = k1_xboole_0 )
      & ( k9_mcart_1(X59,X60,X61,X62,X63) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X63)))
        | ~ m1_subset_1(X63,k4_zfmisc_1(X59,X60,X61,X62))
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0
        | X62 = k1_xboole_0 )
      & ( k10_mcart_1(X59,X60,X61,X62,X63) = k2_mcart_1(k1_mcart_1(X63))
        | ~ m1_subset_1(X63,k4_zfmisc_1(X59,X60,X61,X62))
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0
        | X62 = k1_xboole_0 )
      & ( k11_mcart_1(X59,X60,X61,X62,X63) = k2_mcart_1(X63)
        | ~ m1_subset_1(X63,k4_zfmisc_1(X59,X60,X61,X62))
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0
        | X62 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).

fof(c_0_32,plain,(
    ! [X22,X23,X24,X25] : k4_mcart_1(X22,X23,X24,X25) = k4_tarski(k3_mcart_1(X22,X23,X24),X25) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_33,plain,(
    ! [X16,X17,X18] : k3_mcart_1(X16,X17,X18) = k4_tarski(k4_tarski(X16,X17),X18) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_34,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X45,X46,X47,X48,X49] :
      ( ~ m1_subset_1(X49,k4_zfmisc_1(X45,X46,X47,X48))
      | m1_subset_1(k9_mcart_1(X45,X46,X47,X48,X49),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

fof(c_0_38,plain,(
    ! [X40,X41,X42,X43,X44] :
      ( ~ m1_subset_1(X44,k4_zfmisc_1(X40,X41,X42,X43))
      | m1_subset_1(k8_mcart_1(X40,X41,X42,X43,X44),X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

cnf(c_0_39,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_40,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ~ m1_subset_1(X34,k4_zfmisc_1(X30,X31,X32,X33))
      | m1_subset_1(k10_mcart_1(X30,X31,X32,X33,X34),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).

cnf(c_0_41,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X53,X54] :
      ( ~ v1_relat_1(X54)
      | ~ r2_hidden(X53,X54)
      | X53 = k4_tarski(k1_mcart_1(X53),k2_mcart_1(X53)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

cnf(c_0_44,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_45,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_50,plain,(
    ! [X14,X15] : v1_relat_1(k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_51,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_54,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( esk5_0 = X3
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X3,esk3_0)
    | ~ m1_subset_1(X4,esk4_0)
    | esk6_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_57,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_58,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_59,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(esk6_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_44])).

cnf(c_0_60,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1(esk6_0))) = k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_27]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_61,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_24])).

cnf(c_0_63,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_24])).

cnf(c_0_64,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(esk6_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_27]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_65,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_24])).

cnf(c_0_66,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_24])).

fof(c_0_67,plain,(
    ! [X35,X36,X37,X38,X39] :
      ( ~ m1_subset_1(X39,k4_zfmisc_1(X35,X36,X37,X38))
      | m1_subset_1(k11_mcart_1(X35,X36,X37,X38,X39),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).

cnf(c_0_68,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 = X3
    | esk6_0 != k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X3,esk3_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk6_0))),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)) = k1_mcart_1(k1_mcart_1(esk6_0))
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_27])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk6_0))),esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_27]),c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_27])).

cnf(c_0_74,negated_conjecture,
    ( k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) = k2_mcart_1(k1_mcart_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_27]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_75,negated_conjecture,
    ( esk5_0 != k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_76,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_24])).

fof(c_0_78,plain,(
    ! [X55,X56,X57,X58] :
      ( ( X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0
        | k4_zfmisc_1(X55,X56,X57,X58) != k1_xboole_0 )
      & ( X55 != k1_xboole_0
        | k4_zfmisc_1(X55,X56,X57,X58) = k1_xboole_0 )
      & ( X56 != k1_xboole_0
        | k4_zfmisc_1(X55,X56,X57,X58) = k1_xboole_0 )
      & ( X57 != k1_xboole_0
        | k4_zfmisc_1(X55,X56,X57,X58) = k1_xboole_0 )
      & ( X58 != k1_xboole_0
        | k4_zfmisc_1(X55,X56,X57,X58) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_79,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | esk5_0 = X1
    | k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk6_0)),X1),X2) != esk6_0
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72])])).

cnf(c_0_80,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk6_0)),k2_mcart_1(k1_mcart_1(esk6_0))) = k1_mcart_1(esk6_0)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_44]),c_0_61])])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(esk6_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk6_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_75,c_0_74])).

cnf(c_0_83,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[c_0_76,c_0_24])).

cnf(c_0_84,negated_conjecture,
    ( k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) = k2_mcart_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_27]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_85,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | k4_tarski(k1_mcart_1(esk6_0),X1) != esk6_0
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])]),c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | k4_tarski(k1_mcart_1(esk6_0),k2_mcart_1(esk6_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_35]),c_0_61])])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk6_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_27]),c_0_84])).

cnf(c_0_89,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_85,c_0_24])).

cnf(c_0_90,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n015.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 20:31:38 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.33  # No SInE strategy applied
% 0.14/0.33  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.028 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(t81_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X9)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_mcart_1)).
% 0.14/0.40  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.14/0.40  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.14/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.40  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.14/0.40  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.14/0.40  fof(t61_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 0.14/0.40  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.14/0.40  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.14/0.40  fof(dt_k9_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 0.14/0.40  fof(dt_k8_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_mcart_1)).
% 0.14/0.40  fof(dt_k10_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_mcart_1)).
% 0.14/0.40  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 0.14/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.40  fof(dt_k11_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_mcart_1)).
% 0.14/0.40  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.14/0.40  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X9)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t81_mcart_1])).
% 0.14/0.40  fof(c_0_17, plain, ![X26, X27, X28, X29]:k4_zfmisc_1(X26,X27,X28,X29)=k2_zfmisc_1(k3_zfmisc_1(X26,X27,X28),X29), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.14/0.40  fof(c_0_18, plain, ![X19, X20, X21]:k3_zfmisc_1(X19,X20,X21)=k2_zfmisc_1(k2_zfmisc_1(X19,X20),X21), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.14/0.40  fof(c_0_19, negated_conjecture, ![X70, X71, X72, X73]:(m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))&((~m1_subset_1(X70,esk1_0)|(~m1_subset_1(X71,esk2_0)|(~m1_subset_1(X72,esk3_0)|(~m1_subset_1(X73,esk4_0)|(esk6_0!=k4_mcart_1(X70,X71,X72,X73)|esk5_0=X72)))))&((((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&esk5_0!=k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])).
% 0.14/0.40  cnf(c_0_20, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  cnf(c_0_21, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.40  fof(c_0_22, plain, ![X12, X13]:(~m1_subset_1(X12,X13)|(v1_xboole_0(X13)|r2_hidden(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.40  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_24, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.40  fof(c_0_25, plain, ![X11]:(~v1_xboole_0(X11)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.14/0.40  cnf(c_0_26, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.40  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.40  fof(c_0_28, plain, ![X50, X51, X52]:((r2_hidden(k1_mcart_1(X50),X51)|~r2_hidden(X50,k2_zfmisc_1(X51,X52)))&(r2_hidden(k2_mcart_1(X50),X52)|~r2_hidden(X50,k2_zfmisc_1(X51,X52)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.14/0.40  cnf(c_0_29, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.40  cnf(c_0_30, negated_conjecture, (r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.40  fof(c_0_31, plain, ![X59, X60, X61, X62, X63]:((((k8_mcart_1(X59,X60,X61,X62,X63)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X63)))|~m1_subset_1(X63,k4_zfmisc_1(X59,X60,X61,X62))|(X59=k1_xboole_0|X60=k1_xboole_0|X61=k1_xboole_0|X62=k1_xboole_0))&(k9_mcart_1(X59,X60,X61,X62,X63)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X63)))|~m1_subset_1(X63,k4_zfmisc_1(X59,X60,X61,X62))|(X59=k1_xboole_0|X60=k1_xboole_0|X61=k1_xboole_0|X62=k1_xboole_0)))&(k10_mcart_1(X59,X60,X61,X62,X63)=k2_mcart_1(k1_mcart_1(X63))|~m1_subset_1(X63,k4_zfmisc_1(X59,X60,X61,X62))|(X59=k1_xboole_0|X60=k1_xboole_0|X61=k1_xboole_0|X62=k1_xboole_0)))&(k11_mcart_1(X59,X60,X61,X62,X63)=k2_mcart_1(X63)|~m1_subset_1(X63,k4_zfmisc_1(X59,X60,X61,X62))|(X59=k1_xboole_0|X60=k1_xboole_0|X61=k1_xboole_0|X62=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).
% 0.14/0.40  fof(c_0_32, plain, ![X22, X23, X24, X25]:k4_mcart_1(X22,X23,X24,X25)=k4_tarski(k3_mcart_1(X22,X23,X24),X25), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.14/0.40  fof(c_0_33, plain, ![X16, X17, X18]:k3_mcart_1(X16,X17,X18)=k4_tarski(k4_tarski(X16,X17),X18), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.14/0.40  cnf(c_0_34, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.40  cnf(c_0_35, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.40  cnf(c_0_36, plain, (k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.40  fof(c_0_37, plain, ![X45, X46, X47, X48, X49]:(~m1_subset_1(X49,k4_zfmisc_1(X45,X46,X47,X48))|m1_subset_1(k9_mcart_1(X45,X46,X47,X48,X49),X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).
% 0.14/0.40  fof(c_0_38, plain, ![X40, X41, X42, X43, X44]:(~m1_subset_1(X44,k4_zfmisc_1(X40,X41,X42,X43))|m1_subset_1(k8_mcart_1(X40,X41,X42,X43,X44),X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).
% 0.14/0.40  cnf(c_0_39, plain, (k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.40  fof(c_0_40, plain, ![X30, X31, X32, X33, X34]:(~m1_subset_1(X34,k4_zfmisc_1(X30,X31,X32,X33))|m1_subset_1(k10_mcart_1(X30,X31,X32,X33,X34),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).
% 0.14/0.40  cnf(c_0_41, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.40  cnf(c_0_42, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.40  fof(c_0_43, plain, ![X53, X54]:(~v1_relat_1(X54)|(~r2_hidden(X53,X54)|X53=k4_tarski(k1_mcart_1(X53),k2_mcart_1(X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 0.14/0.40  cnf(c_0_44, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.40  cnf(c_0_45, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_36, c_0_24])).
% 0.14/0.40  cnf(c_0_46, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_47, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_48, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_49, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  fof(c_0_50, plain, ![X14, X15]:v1_relat_1(k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.40  cnf(c_0_51, plain, (m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.40  cnf(c_0_52, plain, (m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.40  cnf(c_0_53, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_39, c_0_24])).
% 0.14/0.40  cnf(c_0_54, plain, (m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.40  cnf(c_0_55, plain, (k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.40  cnf(c_0_56, negated_conjecture, (esk5_0=X3|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X3,esk3_0)|~m1_subset_1(X4,esk4_0)|esk6_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_57, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.40  cnf(c_0_58, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.40  cnf(c_0_59, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|r2_hidden(k1_mcart_1(k1_mcart_1(esk6_0)),k2_zfmisc_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_44])).
% 0.14/0.40  cnf(c_0_60, negated_conjecture, (k2_mcart_1(k1_mcart_1(k1_mcart_1(esk6_0)))=k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_27]), c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.14/0.40  cnf(c_0_61, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.14/0.40  cnf(c_0_62, plain, (m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[c_0_51, c_0_24])).
% 0.14/0.40  cnf(c_0_63, plain, (m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[c_0_52, c_0_24])).
% 0.14/0.40  cnf(c_0_64, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk6_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_27]), c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.14/0.40  cnf(c_0_65, plain, (m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[c_0_54, c_0_24])).
% 0.14/0.40  cnf(c_0_66, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5))|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_55, c_0_24])).
% 0.14/0.40  fof(c_0_67, plain, ![X35, X36, X37, X38, X39]:(~m1_subset_1(X39,k4_zfmisc_1(X35,X36,X37,X38))|m1_subset_1(k11_mcart_1(X35,X36,X37,X38,X39),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).
% 0.14/0.40  cnf(c_0_68, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.40  cnf(c_0_69, negated_conjecture, (esk5_0=X3|esk6_0!=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X3,esk3_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.14/0.40  cnf(c_0_70, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk6_0))),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0))=k1_mcart_1(k1_mcart_1(esk6_0))|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61])])).
% 0.14/0.40  cnf(c_0_71, negated_conjecture, (m1_subset_1(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_27])).
% 0.14/0.40  cnf(c_0_72, negated_conjecture, (m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk6_0))),esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_27]), c_0_64])).
% 0.14/0.40  cnf(c_0_73, negated_conjecture, (m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk3_0)), inference(spm,[status(thm)],[c_0_65, c_0_27])).
% 0.14/0.40  cnf(c_0_74, negated_conjecture, (k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)=k2_mcart_1(k1_mcart_1(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_27]), c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.14/0.40  cnf(c_0_75, negated_conjecture, (esk5_0!=k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_76, plain, (m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.14/0.40  cnf(c_0_77, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_68, c_0_24])).
% 0.14/0.40  fof(c_0_78, plain, ![X55, X56, X57, X58]:((X55=k1_xboole_0|X56=k1_xboole_0|X57=k1_xboole_0|X58=k1_xboole_0|k4_zfmisc_1(X55,X56,X57,X58)!=k1_xboole_0)&((((X55!=k1_xboole_0|k4_zfmisc_1(X55,X56,X57,X58)=k1_xboole_0)&(X56!=k1_xboole_0|k4_zfmisc_1(X55,X56,X57,X58)=k1_xboole_0))&(X57!=k1_xboole_0|k4_zfmisc_1(X55,X56,X57,X58)=k1_xboole_0))&(X58!=k1_xboole_0|k4_zfmisc_1(X55,X56,X57,X58)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.14/0.40  cnf(c_0_79, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|esk5_0=X1|k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk6_0)),X1),X2)!=esk6_0|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_72])])).
% 0.14/0.40  cnf(c_0_80, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk6_0)),k2_mcart_1(k1_mcart_1(esk6_0)))=k1_mcart_1(esk6_0)|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_44]), c_0_61])])).
% 0.14/0.40  cnf(c_0_81, negated_conjecture, (m1_subset_1(k2_mcart_1(k1_mcart_1(esk6_0)),esk3_0)), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.14/0.40  cnf(c_0_82, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk6_0))!=esk5_0), inference(rw,[status(thm)],[c_0_75, c_0_74])).
% 0.14/0.40  cnf(c_0_83, plain, (m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[c_0_76, c_0_24])).
% 0.14/0.40  cnf(c_0_84, negated_conjecture, (k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)=k2_mcart_1(esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_27]), c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.14/0.40  cnf(c_0_85, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.14/0.40  cnf(c_0_86, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|k4_tarski(k1_mcart_1(esk6_0),X1)!=esk6_0|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])]), c_0_82])).
% 0.14/0.40  cnf(c_0_87, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|k4_tarski(k1_mcart_1(esk6_0),k2_mcart_1(esk6_0))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_35]), c_0_61])])).
% 0.14/0.40  cnf(c_0_88, negated_conjecture, (m1_subset_1(k2_mcart_1(esk6_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_27]), c_0_84])).
% 0.14/0.40  cnf(c_0_89, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_85, c_0_24])).
% 0.14/0.40  cnf(c_0_90, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])])).
% 0.14/0.40  cnf(c_0_91, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 92
% 0.14/0.40  # Proof object clause steps            : 59
% 0.14/0.40  # Proof object formula steps           : 33
% 0.14/0.40  # Proof object conjectures             : 33
% 0.14/0.40  # Proof object clause conjectures      : 30
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 25
% 0.14/0.40  # Proof object initial formulas used   : 16
% 0.14/0.40  # Proof object generating inferences   : 19
% 0.14/0.40  # Proof object simplifying inferences  : 52
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 16
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 30
% 0.14/0.40  # Removed in clause preprocessing      : 4
% 0.14/0.40  # Initial clauses in saturation        : 26
% 0.14/0.40  # Processed clauses                    : 257
% 0.14/0.40  # ...of these trivial                  : 17
% 0.14/0.40  # ...subsumed                          : 28
% 0.14/0.40  # ...remaining for further processing  : 212
% 0.14/0.40  # Other redundant clauses eliminated   : 18
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 11
% 0.14/0.40  # Backward-rewritten                   : 23
% 0.14/0.40  # Generated clauses                    : 1958
% 0.14/0.40  # ...of the previous two non-trivial   : 1829
% 0.14/0.40  # Contextual simplify-reflections      : 2
% 0.14/0.40  # Paramodulations                      : 1898
% 0.14/0.40  # Factorizations                       : 42
% 0.14/0.40  # Equation resolutions                 : 18
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 148
% 0.14/0.40  #    Positive orientable unit clauses  : 15
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 5
% 0.14/0.40  #    Non-unit-clauses                  : 128
% 0.14/0.40  # Current number of unprocessed clauses: 872
% 0.14/0.40  # ...number of literals in the above   : 3589
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 64
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 2316
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 1966
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 38
% 0.14/0.40  # Unit Clause-clause subsumption calls : 14
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 19
% 0.14/0.40  # BW rewrite match successes           : 8
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 30849
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.065 s
% 0.14/0.40  # System time              : 0.003 s
% 0.14/0.40  # Total time               : 0.068 s
% 0.14/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
