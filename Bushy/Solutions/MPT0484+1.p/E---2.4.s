%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t79_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:05 EDT 2019

% Result     : Theorem 270.69s
% Output     : CNFRefutation 270.69s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 326 expanded)
%              Number of clauses        :   48 ( 152 expanded)
%              Number of leaves         :   16 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :  296 (1207 expanded)
%              Number of equality atoms :   62 ( 252 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',d10_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',d10_xboole_0)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',t76_relat_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',t8_boole)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',dt_k5_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',dt_k6_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',d3_relat_1)).

fof(t79_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',t79_relat_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',dt_o_0_0_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',t3_subset)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',d5_relat_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',existence_m1_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t79_relat_1.p',t5_subset)).

fof(c_0_16,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X13,X11)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( X13 = X14
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(X15,X11)
        | X15 != X16
        | r2_hidden(k4_tarski(X15,X16),X12)
        | X12 != k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X11,X12),esk4_2(X11,X12)),X12)
        | ~ r2_hidden(esk3_2(X11,X12),X11)
        | esk3_2(X11,X12) != esk4_2(X11,X12)
        | X12 = k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk3_2(X11,X12),X11)
        | r2_hidden(k4_tarski(esk3_2(X11,X12),esk4_2(X11,X12)),X12)
        | X12 = k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( esk3_2(X11,X12) = esk4_2(X11,X12)
        | r2_hidden(k4_tarski(esk3_2(X11,X12),esk4_2(X11,X12)),X12)
        | X12 = k6_relat_1(X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_17,plain,(
    ! [X19,X20] :
      ( ( r1_tarski(X19,X20)
        | X19 != X20 )
      & ( r1_tarski(X20,X19)
        | X19 != X20 )
      & ( ~ r1_tarski(X19,X20)
        | ~ r1_tarski(X20,X19)
        | X19 = X20 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_18,plain,(
    ! [X70,X71] :
      ( ( r1_tarski(k5_relat_1(X71,k6_relat_1(X70)),X71)
        | ~ v1_relat_1(X71) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X70),X71),X71)
        | ~ v1_relat_1(X71) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_19,plain,(
    ! [X74,X75] :
      ( ~ v1_xboole_0(X74)
      | X74 = X75
      | ~ v1_xboole_0(X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_20,plain,(
    ! [X39,X40,X41,X42,X43,X45,X46,X47,X50] :
      ( ( r2_hidden(k4_tarski(X42,esk10_5(X39,X40,X41,X42,X43)),X39)
        | ~ r2_hidden(k4_tarski(X42,X43),X41)
        | X41 != k5_relat_1(X39,X40)
        | ~ v1_relat_1(X41)
        | ~ v1_relat_1(X40)
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(k4_tarski(esk10_5(X39,X40,X41,X42,X43),X43),X40)
        | ~ r2_hidden(k4_tarski(X42,X43),X41)
        | X41 != k5_relat_1(X39,X40)
        | ~ v1_relat_1(X41)
        | ~ v1_relat_1(X40)
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(k4_tarski(X45,X47),X39)
        | ~ r2_hidden(k4_tarski(X47,X46),X40)
        | r2_hidden(k4_tarski(X45,X46),X41)
        | X41 != k5_relat_1(X39,X40)
        | ~ v1_relat_1(X41)
        | ~ v1_relat_1(X40)
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(k4_tarski(esk11_3(X39,X40,X41),esk12_3(X39,X40,X41)),X41)
        | ~ r2_hidden(k4_tarski(esk11_3(X39,X40,X41),X50),X39)
        | ~ r2_hidden(k4_tarski(X50,esk12_3(X39,X40,X41)),X40)
        | X41 = k5_relat_1(X39,X40)
        | ~ v1_relat_1(X41)
        | ~ v1_relat_1(X40)
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(k4_tarski(esk11_3(X39,X40,X41),esk13_3(X39,X40,X41)),X39)
        | r2_hidden(k4_tarski(esk11_3(X39,X40,X41),esk12_3(X39,X40,X41)),X41)
        | X41 = k5_relat_1(X39,X40)
        | ~ v1_relat_1(X41)
        | ~ v1_relat_1(X40)
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(k4_tarski(esk13_3(X39,X40,X41),esk12_3(X39,X40,X41)),X40)
        | r2_hidden(k4_tarski(esk11_3(X39,X40,X41),esk12_3(X39,X40,X41)),X41)
        | X41 = k5_relat_1(X39,X40)
        | ~ v1_relat_1(X41)
        | ~ v1_relat_1(X40)
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_21,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X52)
      | ~ v1_relat_1(X53)
      | v1_relat_1(k5_relat_1(X52,X53)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X54] : v1_relat_1(k6_relat_1(X54)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r1_tarski(X21,X22)
        | ~ r2_hidden(k4_tarski(X23,X24),X21)
        | r2_hidden(k4_tarski(X23,X24),X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk5_2(X21,X25),esk6_2(X21,X25)),X21)
        | r1_tarski(X21,X25)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X21,X25),esk6_2(X21,X25)),X25)
        | r1_tarski(X21,X25)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k2_relat_1(X2),X1)
         => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t79_relat_1])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_30,plain,(
    ! [X59,X60] :
      ( ~ m1_subset_1(X59,X60)
      | v1_xboole_0(X60)
      | r2_hidden(X59,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_31,plain,(
    ! [X63,X64,X65] :
      ( ~ r2_hidden(X63,X64)
      | ~ m1_subset_1(X64,k1_zfmisc_1(X65))
      | m1_subset_1(X63,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_32,plain,(
    ! [X61,X62] :
      ( ( ~ m1_subset_1(X61,k1_zfmisc_1(X62))
        | r1_tarski(X61,X62) )
      & ( ~ r1_tarski(X61,X62)
        | m1_subset_1(X61,k1_zfmisc_1(X62)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,X1),X2)
    | X2 != k6_relat_1(X3)
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ r1_tarski(X1,k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_39,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(k2_relat_1(esk2_0),esk1_0)
    & k5_relat_1(esk2_0,k6_relat_1(esk1_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_40,plain,
    ( o_0_0_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,plain,(
    ! [X28,X29,X30,X32,X33,X34,X35,X37] :
      ( ( ~ r2_hidden(X30,X29)
        | r2_hidden(k4_tarski(esk7_3(X28,X29,X30),X30),X28)
        | X29 != k2_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(X33,X32),X28)
        | r2_hidden(X32,X29)
        | X29 != k2_relat_1(X28) )
      & ( ~ r2_hidden(esk8_2(X34,X35),X35)
        | ~ r2_hidden(k4_tarski(X37,esk8_2(X34,X35)),X34)
        | X35 = k2_relat_1(X34) )
      & ( r2_hidden(esk8_2(X34,X35),X35)
        | r2_hidden(k4_tarski(esk9_2(X34,X35),esk8_2(X34,X35)),X34)
        | X35 = k2_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_45,plain,(
    ! [X55] : m1_subset_1(esk14_1(X55),X55) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_46,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_36])])).

cnf(c_0_48,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | r2_hidden(k4_tarski(esk5_2(X1,k5_relat_1(X1,k6_relat_1(X2))),esk6_2(X1,k5_relat_1(X1,k6_relat_1(X2)))),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( o_0_0_xboole_0 = X1
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_53,plain,(
    ! [X66,X67,X68] :
      ( ~ r2_hidden(X66,X67)
      | ~ m1_subset_1(X67,k1_zfmisc_1(X68))
      | ~ v1_xboole_0(X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_54,plain,
    ( X1 = X2
    | r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_41])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk14_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_57,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,k6_relat_1(X4)))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_36])])).

cnf(c_0_58,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = esk2_0
    | r2_hidden(k4_tarski(esk5_2(esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk6_2(esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1)))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,plain,
    ( o_0_0_xboole_0 = X1
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( X1 = X2
    | r2_hidden(esk14_1(X2),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ r2_hidden(k4_tarski(esk5_2(X1,k5_relat_1(X1,k6_relat_1(X2))),esk6_2(X1,k5_relat_1(X1,k6_relat_1(X2)))),k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = esk2_0
    | r2_hidden(k4_tarski(esk5_2(esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk6_2(esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1)))),k5_relat_1(esk2_0,k6_relat_1(X2)))
    | ~ r2_hidden(esk6_2(esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_49])])).

cnf(c_0_66,negated_conjecture,
    ( o_0_0_xboole_0 = esk1_0
    | r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X1,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = esk2_0
    | r2_hidden(esk6_2(esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_58])).

cnf(c_0_68,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_43])).

cnf(c_0_69,plain,
    ( o_0_0_xboole_0 = X1
    | r2_hidden(esk14_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_29])).

cnf(c_0_70,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = esk2_0
    | ~ r2_hidden(esk6_2(esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_49])])).

cnf(c_0_71,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = esk2_0
    | o_0_0_xboole_0 = esk1_0
    | r2_hidden(esk6_2(esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk1_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(esk1_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_73,plain,
    ( o_0_0_xboole_0 = X1
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( o_0_0_xboole_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( k2_relat_1(esk2_0) = o_0_0_xboole_0
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_60])).

cnf(c_0_76,plain,
    ( v1_xboole_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(k2_relat_1(esk2_0))) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_74]),c_0_76])])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
