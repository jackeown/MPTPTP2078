%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t87_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:15 EDT 2019

% Result     : Theorem 273.09s
% Output     : CNFRefutation 273.09s
% Verified   : 
% Statistics : Number of formulae       :  136 (1018 expanded)
%              Number of clauses        :  103 ( 492 expanded)
%              Number of leaves         :   17 ( 278 expanded)
%              Depth                    :   13
%              Number of atoms          :  492 (3864 expanded)
%              Number of equality atoms :  247 (1093 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   48 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t8_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t2_subset)).

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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t87_mcart_1)).

fof(dt_k11_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',dt_k11_mcart_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t1_subset)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t55_mcart_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t7_boole)).

fof(dt_k10_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',dt_k10_mcart_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',d2_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t6_boole)).

fof(dt_k8_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',dt_k8_mcart_1)).

fof(t86_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & X5 != k1_xboole_0
        & X6 != k1_xboole_0
        & X7 != k1_xboole_0
        & X8 != k1_xboole_0
        & ? [X9] :
            ( m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))
            & ? [X10] :
                ( m1_subset_1(X10,k4_zfmisc_1(X5,X6,X7,X8))
                & X9 = X10
                & ~ ( k8_mcart_1(X1,X2,X3,X4,X9) = k8_mcart_1(X5,X6,X7,X8,X10)
                    & k9_mcart_1(X1,X2,X3,X4,X9) = k9_mcart_1(X5,X6,X7,X8,X10)
                    & k10_mcart_1(X1,X2,X3,X4,X9) = k10_mcart_1(X5,X6,X7,X8,X10)
                    & k11_mcart_1(X1,X2,X3,X4,X9) = k11_mcart_1(X5,X6,X7,X8,X10) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t86_mcart_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',existence_m1_subset_1)).

fof(dt_k9_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',dt_k9_mcart_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t87_mcart_1.p',t4_subset)).

fof(c_0_17,plain,(
    ! [X73,X74] :
      ( ~ v1_xboole_0(X73)
      | X73 = X74
      | ~ v1_xboole_0(X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_18,plain,(
    ! [X46,X47] :
      ( ~ m1_subset_1(X46,X47)
      | v1_xboole_0(X47)
      | r2_hidden(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_19,negated_conjecture,(
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

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ~ m1_subset_1(X31,k4_zfmisc_1(X27,X28,X29,X30))
      | m1_subset_1(k11_mcart_1(X27,X28,X29,X30,X31),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).

fof(c_0_23,plain,(
    ! [X44,X45] :
      ( ~ r2_hidden(X44,X45)
      | m1_subset_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk9_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
    & r2_hidden(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
    & ( ~ r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk5_0)
      | ~ r2_hidden(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk6_0)
      | ~ r2_hidden(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0)
      | ~ r2_hidden(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_25,plain,(
    ! [X53,X54,X55,X56] :
      ( ( X53 = k1_xboole_0
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0
        | k4_zfmisc_1(X53,X54,X55,X56) != k1_xboole_0 )
      & ( X53 != k1_xboole_0
        | k4_zfmisc_1(X53,X54,X55,X56) = k1_xboole_0 )
      & ( X54 != k1_xboole_0
        | k4_zfmisc_1(X53,X54,X55,X56) = k1_xboole_0 )
      & ( X55 != k1_xboole_0
        | k4_zfmisc_1(X53,X54,X55,X56) = k1_xboole_0 )
      & ( X56 != k1_xboole_0
        | k4_zfmisc_1(X53,X54,X55,X56) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

fof(c_0_26,plain,(
    ! [X61,X62] :
      ( ~ r2_hidden(X61,X62)
      | ~ v1_xboole_0(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_27,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ~ m1_subset_1(X26,k4_zfmisc_1(X22,X23,X24,X25))
      | m1_subset_1(k10_mcart_1(X22,X23,X24,X25,X26),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | r2_hidden(X3,X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X3,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_34,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

fof(c_0_35,plain,(
    ! [X60] :
      ( ~ v1_xboole_0(X60)
      | X60 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_36,plain,(
    ! [X32,X33,X34,X35,X36] :
      ( ~ m1_subset_1(X36,k4_zfmisc_1(X32,X33,X34,X35))
      | m1_subset_1(k8_mcart_1(X32,X33,X34,X35,X36),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

fof(c_0_37,plain,(
    ! [X63,X64,X65,X66,X67,X68,X69,X70,X71,X72] :
      ( ( k8_mcart_1(X63,X64,X65,X66,X71) = k8_mcart_1(X67,X68,X69,X70,X72)
        | ~ m1_subset_1(X72,k4_zfmisc_1(X67,X68,X69,X70))
        | X71 != X72
        | ~ m1_subset_1(X71,k4_zfmisc_1(X63,X64,X65,X66))
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0
        | X65 = k1_xboole_0
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | X70 = k1_xboole_0 )
      & ( k9_mcart_1(X63,X64,X65,X66,X71) = k9_mcart_1(X67,X68,X69,X70,X72)
        | ~ m1_subset_1(X72,k4_zfmisc_1(X67,X68,X69,X70))
        | X71 != X72
        | ~ m1_subset_1(X71,k4_zfmisc_1(X63,X64,X65,X66))
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0
        | X65 = k1_xboole_0
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | X70 = k1_xboole_0 )
      & ( k10_mcart_1(X63,X64,X65,X66,X71) = k10_mcart_1(X67,X68,X69,X70,X72)
        | ~ m1_subset_1(X72,k4_zfmisc_1(X67,X68,X69,X70))
        | X71 != X72
        | ~ m1_subset_1(X71,k4_zfmisc_1(X63,X64,X65,X66))
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0
        | X65 = k1_xboole_0
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | X70 = k1_xboole_0 )
      & ( k11_mcart_1(X63,X64,X65,X66,X71) = k11_mcart_1(X67,X68,X69,X70,X72)
        | ~ m1_subset_1(X72,k4_zfmisc_1(X67,X68,X69,X70))
        | X71 != X72
        | ~ m1_subset_1(X71,k4_zfmisc_1(X63,X64,X65,X66))
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0
        | X65 = k1_xboole_0
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0
        | X68 = k1_xboole_0
        | X69 = k1_xboole_0
        | X70 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_mcart_1])])])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_39,plain,(
    ! [X57,X58,X59] :
      ( ~ r2_hidden(X57,X58)
      | ~ m1_subset_1(X58,k1_zfmisc_1(X59))
      | ~ v1_xboole_0(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_40,plain,(
    ! [X42] : m1_subset_1(esk10_1(X42),X42) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_41,plain,(
    ! [X37,X38,X39,X40,X41] :
      ( ~ m1_subset_1(X41,k4_zfmisc_1(X37,X38,X39,X40))
      | m1_subset_1(k9_mcart_1(X37,X38,X39,X40,X41),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

cnf(c_0_42,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_43,plain,(
    ! [X50,X51,X52] :
      ( ~ r2_hidden(X50,X51)
      | ~ m1_subset_1(X51,k1_zfmisc_1(X52))
      | m1_subset_1(X50,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_44,plain,
    ( X1 = X2
    | r2_hidden(k11_mcart_1(X3,X4,X5,X1,X6),X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X3,X4,X5,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk9_0,k1_xboole_0)
    | esk8_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = k8_mcart_1(X6,X7,X8,X9,X10)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | X8 = k1_xboole_0
    | X9 = k1_xboole_0
    | ~ m1_subset_1(X10,k4_zfmisc_1(X6,X7,X8,X9))
    | X5 != X10
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_52,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_53,plain,
    ( k4_zfmisc_1(X2,X1,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_54,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_55,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = k9_mcart_1(X6,X7,X8,X9,X10)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | X8 = k1_xboole_0
    | X9 = k1_xboole_0
    | ~ m1_subset_1(X10,k4_zfmisc_1(X6,X7,X8,X9))
    | X5 != X10
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_56,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = k10_mcart_1(X6,X7,X8,X9,X10)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | X8 = k1_xboole_0
    | X9 = k1_xboole_0
    | ~ m1_subset_1(X10,k4_zfmisc_1(X6,X7,X8,X9))
    | X5 != X10
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_57,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k11_mcart_1(X6,X7,X8,X9,X10)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | X8 = k1_xboole_0
    | X9 = k1_xboole_0
    | ~ m1_subset_1(X10,k4_zfmisc_1(X6,X7,X8,X9))
    | X5 != X10
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk10_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_60,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_61,plain,
    ( X1 = X2
    | r2_hidden(k10_mcart_1(X3,X4,X1,X5,X6),X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X3,X4,X1,X5)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_64,negated_conjecture,
    ( esk8_0 = X1
    | r2_hidden(k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk8_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_65,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_46]),c_0_47])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk5_0)
    | ~ r2_hidden(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk6_0)
    | ~ r2_hidden(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0)
    | ~ r2_hidden(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_21])).

cnf(c_0_68,plain,
    ( X1 = X2
    | r2_hidden(k8_mcart_1(X1,X3,X4,X5,X6),X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X3,X4,X5)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_49])).

cnf(c_0_69,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = k8_mcart_1(X6,X7,X8,X9,X5)
    | X9 = k1_xboole_0
    | X8 = k1_xboole_0
    | X7 = k1_xboole_0
    | X6 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X6,X7,X8,X9))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_70,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_47])])).

cnf(c_0_71,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_53]),c_0_47])])).

cnf(c_0_72,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_54]),c_0_47])])).

cnf(c_0_73,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = k9_mcart_1(X6,X7,X8,X9,X5)
    | X9 = k1_xboole_0
    | X8 = k1_xboole_0
    | X7 = k1_xboole_0
    | X6 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X6,X7,X8,X9))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_74,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = k10_mcart_1(X6,X7,X8,X9,X5)
    | X9 = k1_xboole_0
    | X8 = k1_xboole_0
    | X7 = k1_xboole_0
    | X6 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X6,X7,X8,X9))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_75,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k11_mcart_1(X6,X7,X8,X9,X5)
    | X9 = k1_xboole_0
    | X8 = k1_xboole_0
    | X7 = k1_xboole_0
    | X6 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X6,X7,X8,X9))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_76,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk10_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_77,plain,
    ( X1 = X2
    | r2_hidden(k9_mcart_1(X3,X1,X4,X5,X6),X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X3,X1,X4,X5)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_60])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_79,negated_conjecture,
    ( esk7_0 = X1
    | r2_hidden(k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_45])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_62])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_62])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_47]),c_0_65])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk5_0)
    | ~ r2_hidden(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk6_0)
    | ~ r2_hidden(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0)
    | ~ m1_subset_1(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_65])).

cnf(c_0_84,negated_conjecture,
    ( esk5_0 = X1
    | r2_hidden(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_45])).

cnf(c_0_85,negated_conjecture,
    ( k8_mcart_1(X1,X2,X3,X4,esk9_0) = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(esk9_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_45]),c_0_65]),c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk9_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_87,negated_conjecture,
    ( k9_mcart_1(X1,X2,X3,X4,esk9_0) = k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(esk9_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_45]),c_0_65]),c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_88,negated_conjecture,
    ( k10_mcart_1(X1,X2,X3,X4,esk9_0) = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(esk9_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_45]),c_0_65]),c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_89,negated_conjecture,
    ( k11_mcart_1(X1,X2,X3,X4,esk9_0) = k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(esk9_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_45]),c_0_65]),c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_90,plain,
    ( esk10_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,esk10_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_67])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_93,negated_conjecture,
    ( esk6_0 = X1
    | r2_hidden(k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_45])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_78])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_78])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_47]),c_0_70])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_21])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk5_0)
    | ~ r2_hidden(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk6_0)
    | ~ m1_subset_1(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0)
    | ~ m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_67]),c_0_70])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_47]),c_0_72])).

cnf(c_0_101,negated_conjecture,
    ( k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_102,negated_conjecture,
    ( k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_86])).

cnf(c_0_103,negated_conjecture,
    ( k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_86])).

cnf(c_0_104,negated_conjecture,
    ( k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_89,c_0_86])).

cnf(c_0_105,plain,
    ( esk10_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_59])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_91])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_92])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_92])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_47]),c_0_71])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_21])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk4_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_113,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk5_0)
    | ~ m1_subset_1(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0)
    | ~ m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0)
    | ~ m1_subset_1(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_67]),c_0_71])).

cnf(c_0_114,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_115,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | m1_subset_1(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_102]),c_0_45])])).

cnf(c_0_116,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_103]),c_0_45])])).

cnf(c_0_117,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | m1_subset_1(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_104]),c_0_45])])).

cnf(c_0_118,plain,
    ( esk10_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_105,c_0_47])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X2,esk5_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_21])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X2,esk6_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_21])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk3_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_82])).

cnf(c_0_124,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115]),c_0_116]),c_0_117])).

cnf(c_0_125,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_118]),c_0_47])])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk10_1(esk1_0),esk1_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_59])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk2_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_96])).

cnf(c_0_129,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk10_1(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_100])).

cnf(c_0_131,negated_conjecture,
    ( r2_hidden(k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_127,c_0_109])).

cnf(c_0_132,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_125])).

cnf(c_0_133,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_130])).

cnf(c_0_134,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_125])).

cnf(c_0_135,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_134]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
