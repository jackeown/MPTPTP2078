%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 354 expanded)
%              Number of clauses        :   53 ( 179 expanded)
%              Number of leaves         :   12 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  331 (2872 expanded)
%              Number of equality atoms :   62 (1057 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

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

fof(d1_funct_1,axiom,(
    ! [X1] :
      ( v1_funct_1(X1)
    <=> ! [X2,X3,X4] :
          ( ( r2_hidden(k4_tarski(X2,X3),X1)
            & r2_hidden(k4_tarski(X2,X4),X1) )
         => X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_1)).

fof(t121_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

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

fof(c_0_12,plain,(
    ! [X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(k4_tarski(esk2_3(X12,X13,X14),X14),X12)
        | X13 != k2_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(X17,X16),X12)
        | r2_hidden(X16,X13)
        | X13 != k2_relat_1(X12) )
      & ( ~ r2_hidden(esk3_2(X18,X19),X19)
        | ~ r2_hidden(k4_tarski(X21,esk3_2(X18,X19)),X18)
        | X19 = k2_relat_1(X18) )
      & ( r2_hidden(esk3_2(X18,X19),X19)
        | r2_hidden(k4_tarski(esk4_2(X18,X19),esk3_2(X18,X19)),X18)
        | X19 = k2_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_13,plain,(
    ! [X53,X54,X55,X56,X58,X59,X60,X61,X62,X64] :
      ( ( v1_relat_1(esk11_4(X53,X54,X55,X56))
        | ~ r2_hidden(X56,X55)
        | X55 != k1_funct_2(X53,X54) )
      & ( v1_funct_1(esk11_4(X53,X54,X55,X56))
        | ~ r2_hidden(X56,X55)
        | X55 != k1_funct_2(X53,X54) )
      & ( X56 = esk11_4(X53,X54,X55,X56)
        | ~ r2_hidden(X56,X55)
        | X55 != k1_funct_2(X53,X54) )
      & ( k1_relat_1(esk11_4(X53,X54,X55,X56)) = X53
        | ~ r2_hidden(X56,X55)
        | X55 != k1_funct_2(X53,X54) )
      & ( r1_tarski(k2_relat_1(esk11_4(X53,X54,X55,X56)),X54)
        | ~ r2_hidden(X56,X55)
        | X55 != k1_funct_2(X53,X54) )
      & ( ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59)
        | X58 != X59
        | k1_relat_1(X59) != X53
        | ~ r1_tarski(k2_relat_1(X59),X54)
        | r2_hidden(X58,X55)
        | X55 != k1_funct_2(X53,X54) )
      & ( ~ r2_hidden(esk12_3(X60,X61,X62),X62)
        | ~ v1_relat_1(X64)
        | ~ v1_funct_1(X64)
        | esk12_3(X60,X61,X62) != X64
        | k1_relat_1(X64) != X60
        | ~ r1_tarski(k2_relat_1(X64),X61)
        | X62 = k1_funct_2(X60,X61) )
      & ( v1_relat_1(esk13_3(X60,X61,X62))
        | r2_hidden(esk12_3(X60,X61,X62),X62)
        | X62 = k1_funct_2(X60,X61) )
      & ( v1_funct_1(esk13_3(X60,X61,X62))
        | r2_hidden(esk12_3(X60,X61,X62),X62)
        | X62 = k1_funct_2(X60,X61) )
      & ( esk12_3(X60,X61,X62) = esk13_3(X60,X61,X62)
        | r2_hidden(esk12_3(X60,X61,X62),X62)
        | X62 = k1_funct_2(X60,X61) )
      & ( k1_relat_1(esk13_3(X60,X61,X62)) = X60
        | r2_hidden(esk12_3(X60,X61,X62),X62)
        | X62 = k1_funct_2(X60,X61) )
      & ( r1_tarski(k2_relat_1(esk13_3(X60,X61,X62)),X61)
        | r2_hidden(esk12_3(X60,X61,X62),X62)
        | X62 = k1_funct_2(X60,X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X33,X34,X35,X36,X37] :
      ( ( ~ v1_funct_1(X33)
        | ~ r2_hidden(k4_tarski(X34,X35),X33)
        | ~ r2_hidden(k4_tarski(X34,X36),X33)
        | X35 = X36 )
      & ( r2_hidden(k4_tarski(esk8_1(X37),esk9_1(X37)),X37)
        | v1_funct_1(X37) )
      & ( r2_hidden(k4_tarski(esk8_1(X37),esk10_1(X37)),X37)
        | v1_funct_1(X37) )
      & ( esk9_1(X37) != esk10_1(X37)
        | v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_1])])])])])])).

cnf(c_0_16,plain,
    ( v1_funct_1(esk11_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( X1 = esk11_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

fof(c_0_19,plain,(
    ! [X23,X24,X25,X27,X28,X29,X31] :
      ( ( r2_hidden(esk5_3(X23,X24,X25),k1_relat_1(X23))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( X25 = k1_funct_1(X23,esk5_3(X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(X28,k1_relat_1(X23))
        | X27 != k1_funct_1(X23,X28)
        | r2_hidden(X27,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(esk6_2(X23,X29),X29)
        | ~ r2_hidden(X31,k1_relat_1(X23))
        | esk6_2(X23,X29) != k1_funct_1(X23,X31)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( r2_hidden(esk7_2(X23,X29),k1_relat_1(X23))
        | r2_hidden(esk6_2(X23,X29),X29)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( esk6_2(X23,X29) = k1_funct_1(X23,esk7_2(X23,X29))
        | r2_hidden(esk6_2(X23,X29),X29)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_20,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk8_1(X1),esk9_1(X1)),X1)
    | v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_relat_1(esk11_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( v1_relat_1(esk11_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( v1_funct_1(esk11_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( esk11_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_27,negated_conjecture,
    ( r2_hidden(esk16_0,k1_funct_2(esk14_0,esk15_0))
    & ( ~ v1_funct_1(esk16_0)
      | ~ v1_funct_2(esk16_0,esk14_0,esk15_0)
      | ~ m1_subset_1(esk16_0,k1_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( v1_funct_1(X1)
    | r2_hidden(esk9_1(X1),k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( k1_relat_1(esk11_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( v1_relat_1(esk11_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk16_0,k1_funct_2(esk14_0,esk15_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_relat_1(esk11_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).

cnf(c_0_37,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_38,plain,(
    ! [X66] :
      ( ( v1_funct_1(X66)
        | ~ v1_relat_1(X66)
        | ~ v1_funct_1(X66) )
      & ( v1_funct_2(X66,k1_relat_1(X66),k2_relat_1(X66))
        | ~ v1_relat_1(X66)
        | ~ v1_funct_1(X66) )
      & ( m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X66),k2_relat_1(X66))))
        | ~ v1_relat_1(X66)
        | ~ v1_funct_1(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_39,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_40,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

fof(c_0_41,plain,(
    ! [X47,X48,X49] :
      ( ~ v1_xboole_0(X47)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | v1_partfun1(X49,X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_funct_1(esk16_0)
    | ~ v1_funct_2(esk16_0,esk14_0,esk15_0)
    | ~ m1_subset_1(esk16_0,k1_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk16_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_44,plain,(
    ! [X41,X42,X43] :
      ( ~ v1_relat_1(X43)
      | ~ r1_tarski(k1_relat_1(X43),X41)
      | ~ r1_tarski(k2_relat_1(X43),X42)
      | m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_45,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_46,plain,(
    ! [X44,X45,X46] :
      ( ( v1_funct_1(X46)
        | ~ v1_funct_1(X46)
        | ~ v1_partfun1(X46,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( v1_funct_2(X46,X44,X45)
        | ~ v1_funct_1(X46)
        | ~ v1_partfun1(X46,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_relat_1(esk11_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_36]),c_0_37])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_50,plain,(
    ! [X50,X51,X52] :
      ( ( v1_funct_1(X52)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | v1_xboole_0(X51) )
      & ( v1_partfun1(X52,X50)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | v1_xboole_0(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(esk16_0) = esk14_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk16_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_54,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_funct_2(esk16_0,esk14_0,esk15_0)
    | ~ m1_subset_1(esk16_0,k1_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_26])).

cnf(c_0_61,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_62,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk16_0,k1_zfmisc_1(k2_zfmisc_1(esk14_0,k2_relat_1(esk16_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_43]),c_0_53])])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(esk16_0,esk14_0,k2_relat_1(esk16_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_52]),c_0_43]),c_0_53])])).

cnf(c_0_65,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_51])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_funct_2(esk16_0,esk14_0,esk15_0)
    | ~ r1_tarski(k2_relat_1(esk16_0),esk15_0)
    | ~ r1_tarski(k1_relat_1(esk16_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_53])])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X3)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk16_0),esk15_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_34])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(esk14_0)
    | ~ v1_xboole_0(k2_relat_1(esk16_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_52]),c_0_53])])).

cnf(c_0_71,negated_conjecture,
    ( v1_partfun1(esk16_0,esk14_0)
    | v1_xboole_0(k2_relat_1(esk16_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_43])])).

cnf(c_0_72,negated_conjecture,
    ( v1_partfun1(esk16_0,esk14_0)
    | ~ v1_xboole_0(esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_52]),c_0_43]),c_0_53])])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_funct_2(esk16_0,esk14_0,esk15_0)
    | ~ r1_tarski(k2_relat_1(esk16_0),esk15_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_52]),c_0_67])])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk16_0,X1,esk15_0)
    | ~ v1_partfun1(esk16_0,X1)
    | ~ r1_tarski(esk14_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_43]),c_0_53]),c_0_52])])).

cnf(c_0_75,negated_conjecture,
    ( v1_partfun1(esk16_0,esk14_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_funct_2(esk16_0,esk14_0,esk15_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_69])])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_67])]),c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.030 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.40  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 0.19/0.40  fof(d1_funct_1, axiom, ![X1]:(v1_funct_1(X1)<=>![X2, X3, X4]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X2,X4),X1))=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_1)).
% 0.19/0.40  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 0.19/0.41  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.41  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.41  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.19/0.41  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.19/0.41  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.19/0.41  fof(c_0_12, plain, ![X12, X13, X14, X16, X17, X18, X19, X21]:(((~r2_hidden(X14,X13)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),X14),X12)|X13!=k2_relat_1(X12))&(~r2_hidden(k4_tarski(X17,X16),X12)|r2_hidden(X16,X13)|X13!=k2_relat_1(X12)))&((~r2_hidden(esk3_2(X18,X19),X19)|~r2_hidden(k4_tarski(X21,esk3_2(X18,X19)),X18)|X19=k2_relat_1(X18))&(r2_hidden(esk3_2(X18,X19),X19)|r2_hidden(k4_tarski(esk4_2(X18,X19),esk3_2(X18,X19)),X18)|X19=k2_relat_1(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.41  fof(c_0_13, plain, ![X53, X54, X55, X56, X58, X59, X60, X61, X62, X64]:(((((((v1_relat_1(esk11_4(X53,X54,X55,X56))|~r2_hidden(X56,X55)|X55!=k1_funct_2(X53,X54))&(v1_funct_1(esk11_4(X53,X54,X55,X56))|~r2_hidden(X56,X55)|X55!=k1_funct_2(X53,X54)))&(X56=esk11_4(X53,X54,X55,X56)|~r2_hidden(X56,X55)|X55!=k1_funct_2(X53,X54)))&(k1_relat_1(esk11_4(X53,X54,X55,X56))=X53|~r2_hidden(X56,X55)|X55!=k1_funct_2(X53,X54)))&(r1_tarski(k2_relat_1(esk11_4(X53,X54,X55,X56)),X54)|~r2_hidden(X56,X55)|X55!=k1_funct_2(X53,X54)))&(~v1_relat_1(X59)|~v1_funct_1(X59)|X58!=X59|k1_relat_1(X59)!=X53|~r1_tarski(k2_relat_1(X59),X54)|r2_hidden(X58,X55)|X55!=k1_funct_2(X53,X54)))&((~r2_hidden(esk12_3(X60,X61,X62),X62)|(~v1_relat_1(X64)|~v1_funct_1(X64)|esk12_3(X60,X61,X62)!=X64|k1_relat_1(X64)!=X60|~r1_tarski(k2_relat_1(X64),X61))|X62=k1_funct_2(X60,X61))&(((((v1_relat_1(esk13_3(X60,X61,X62))|r2_hidden(esk12_3(X60,X61,X62),X62)|X62=k1_funct_2(X60,X61))&(v1_funct_1(esk13_3(X60,X61,X62))|r2_hidden(esk12_3(X60,X61,X62),X62)|X62=k1_funct_2(X60,X61)))&(esk12_3(X60,X61,X62)=esk13_3(X60,X61,X62)|r2_hidden(esk12_3(X60,X61,X62),X62)|X62=k1_funct_2(X60,X61)))&(k1_relat_1(esk13_3(X60,X61,X62))=X60|r2_hidden(esk12_3(X60,X61,X62),X62)|X62=k1_funct_2(X60,X61)))&(r1_tarski(k2_relat_1(esk13_3(X60,X61,X62)),X61)|r2_hidden(esk12_3(X60,X61,X62),X62)|X62=k1_funct_2(X60,X61))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.19/0.41  cnf(c_0_14, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  fof(c_0_15, plain, ![X33, X34, X35, X36, X37]:((~v1_funct_1(X33)|(~r2_hidden(k4_tarski(X34,X35),X33)|~r2_hidden(k4_tarski(X34,X36),X33)|X35=X36))&(((r2_hidden(k4_tarski(esk8_1(X37),esk9_1(X37)),X37)|v1_funct_1(X37))&(r2_hidden(k4_tarski(esk8_1(X37),esk10_1(X37)),X37)|v1_funct_1(X37)))&(esk9_1(X37)!=esk10_1(X37)|v1_funct_1(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_1])])])])])])).
% 0.19/0.41  cnf(c_0_16, plain, (v1_funct_1(esk11_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_17, plain, (X1=esk11_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.19/0.41  fof(c_0_19, plain, ![X23, X24, X25, X27, X28, X29, X31]:((((r2_hidden(esk5_3(X23,X24,X25),k1_relat_1(X23))|~r2_hidden(X25,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(X25=k1_funct_1(X23,esk5_3(X23,X24,X25))|~r2_hidden(X25,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&(~r2_hidden(X28,k1_relat_1(X23))|X27!=k1_funct_1(X23,X28)|r2_hidden(X27,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&((~r2_hidden(esk6_2(X23,X29),X29)|(~r2_hidden(X31,k1_relat_1(X23))|esk6_2(X23,X29)!=k1_funct_1(X23,X31))|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&((r2_hidden(esk7_2(X23,X29),k1_relat_1(X23))|r2_hidden(esk6_2(X23,X29),X29)|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(esk6_2(X23,X29)=k1_funct_1(X23,esk7_2(X23,X29))|r2_hidden(esk6_2(X23,X29),X29)|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.41  fof(c_0_20, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_21, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk8_1(X1),esk9_1(X1)),X1)|v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_23, plain, (k1_relat_1(esk11_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_24, plain, (v1_relat_1(esk11_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_25, plain, (v1_funct_1(esk11_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_26, plain, (esk11_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.41  fof(c_0_27, negated_conjecture, (r2_hidden(esk16_0,k1_funct_2(esk14_0,esk15_0))&(~v1_funct_1(esk16_0)|~v1_funct_2(esk16_0,esk14_0,esk15_0)|~m1_subset_1(esk16_0,k1_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.19/0.41  cnf(c_0_28, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_29, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_30, plain, (v1_funct_1(X1)|r2_hidden(esk9_1(X1),k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.41  cnf(c_0_31, plain, (k1_relat_1(esk11_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_32, plain, (v1_relat_1(esk11_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_33, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.41  cnf(c_0_34, negated_conjecture, (r2_hidden(esk16_0,k1_funct_2(esk14_0,esk15_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_35, plain, (r1_tarski(k2_relat_1(esk11_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_36, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).
% 0.19/0.41  cnf(c_0_37, plain, (v1_funct_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.41  fof(c_0_38, plain, ![X66]:(((v1_funct_1(X66)|(~v1_relat_1(X66)|~v1_funct_1(X66)))&(v1_funct_2(X66,k1_relat_1(X66),k2_relat_1(X66))|(~v1_relat_1(X66)|~v1_funct_1(X66))))&(m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X66),k2_relat_1(X66))))|(~v1_relat_1(X66)|~v1_funct_1(X66)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.41  cnf(c_0_39, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_31, c_0_26])).
% 0.19/0.41  cnf(c_0_40, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_32, c_0_26])).
% 0.19/0.41  fof(c_0_41, plain, ![X47, X48, X49]:(~v1_xboole_0(X47)|(~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|v1_partfun1(X49,X47))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (~v1_funct_1(esk16_0)|~v1_funct_2(esk16_0,esk14_0,esk15_0)|~m1_subset_1(esk16_0,k1_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (v1_funct_1(esk16_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.41  fof(c_0_44, plain, ![X41, X42, X43]:(~v1_relat_1(X43)|(~r1_tarski(k1_relat_1(X43),X41)|~r1_tarski(k2_relat_1(X43),X42)|m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.19/0.41  fof(c_0_45, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  fof(c_0_46, plain, ![X44, X45, X46]:((v1_funct_1(X46)|(~v1_funct_1(X46)|~v1_partfun1(X46,X44))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(v1_funct_2(X46,X44,X45)|(~v1_funct_1(X46)|~v1_partfun1(X46,X44))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.19/0.41  cnf(c_0_47, plain, (r1_tarski(k2_relat_1(esk11_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_35])).
% 0.19/0.41  cnf(c_0_48, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_xboole_0(k2_relat_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_36]), c_0_37])).
% 0.19/0.41  cnf(c_0_49, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  fof(c_0_50, plain, ![X50, X51, X52]:((v1_funct_1(X52)|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|v1_xboole_0(X51))&(v1_partfun1(X52,X50)|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X51))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|v1_xboole_0(X51))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.19/0.41  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (k1_relat_1(esk16_0)=esk14_0), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk16_0)), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.19/0.41  cnf(c_0_54, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.41  cnf(c_0_55, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (~v1_funct_2(esk16_0,esk14_0,esk15_0)|~m1_subset_1(esk16_0,k1_zfmisc_1(k2_zfmisc_1(esk14_0,esk15_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 0.19/0.41  cnf(c_0_57, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.41  cnf(c_0_58, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.41  cnf(c_0_59, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.41  cnf(c_0_60, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_47, c_0_26])).
% 0.19/0.41  cnf(c_0_61, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.41  cnf(c_0_62, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk16_0,k1_zfmisc_1(k2_zfmisc_1(esk14_0,k2_relat_1(esk16_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_43]), c_0_53])])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, (v1_funct_2(esk16_0,esk14_0,k2_relat_1(esk16_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_52]), c_0_43]), c_0_53])])).
% 0.19/0.41  cnf(c_0_65, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_55, c_0_51])).
% 0.19/0.41  cnf(c_0_66, negated_conjecture, (~v1_funct_2(esk16_0,esk14_0,esk15_0)|~r1_tarski(k2_relat_1(esk16_0),esk15_0)|~r1_tarski(k1_relat_1(esk16_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_53])])).
% 0.19/0.41  cnf(c_0_67, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_58])).
% 0.19/0.41  cnf(c_0_68, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X3)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_59, c_0_57])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (r1_tarski(k2_relat_1(esk16_0),esk15_0)), inference(spm,[status(thm)],[c_0_60, c_0_34])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (v1_xboole_0(esk14_0)|~v1_xboole_0(k2_relat_1(esk16_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_52]), c_0_53])])).
% 0.19/0.41  cnf(c_0_71, negated_conjecture, (v1_partfun1(esk16_0,esk14_0)|v1_xboole_0(k2_relat_1(esk16_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_43])])).
% 0.19/0.41  cnf(c_0_72, negated_conjecture, (v1_partfun1(esk16_0,esk14_0)|~v1_xboole_0(esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_52]), c_0_43]), c_0_53])])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (~v1_funct_2(esk16_0,esk14_0,esk15_0)|~r1_tarski(k2_relat_1(esk16_0),esk15_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_52]), c_0_67])])).
% 0.19/0.41  cnf(c_0_74, negated_conjecture, (v1_funct_2(esk16_0,X1,esk15_0)|~v1_partfun1(esk16_0,X1)|~r1_tarski(esk14_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_43]), c_0_53]), c_0_52])])).
% 0.19/0.41  cnf(c_0_75, negated_conjecture, (v1_partfun1(esk16_0,esk14_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.19/0.41  cnf(c_0_76, negated_conjecture, (~v1_funct_2(esk16_0,esk14_0,esk15_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_69])])).
% 0.19/0.41  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_67])]), c_0_76]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 78
% 0.19/0.41  # Proof object clause steps            : 53
% 0.19/0.41  # Proof object formula steps           : 25
% 0.19/0.41  # Proof object conjectures             : 21
% 0.19/0.41  # Proof object clause conjectures      : 18
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 19
% 0.19/0.41  # Proof object initial formulas used   : 12
% 0.19/0.41  # Proof object generating inferences   : 23
% 0.19/0.41  # Proof object simplifying inferences  : 41
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 12
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 42
% 0.19/0.41  # Removed in clause preprocessing      : 3
% 0.19/0.41  # Initial clauses in saturation        : 39
% 0.19/0.41  # Processed clauses                    : 425
% 0.19/0.41  # ...of these trivial                  : 0
% 0.19/0.41  # ...subsumed                          : 164
% 0.19/0.41  # ...remaining for further processing  : 261
% 0.19/0.41  # Other redundant clauses eliminated   : 17
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 2
% 0.19/0.41  # Backward-rewritten                   : 5
% 0.19/0.41  # Generated clauses                    : 1058
% 0.19/0.41  # ...of the previous two non-trivial   : 1030
% 0.19/0.41  # Contextual simplify-reflections      : 19
% 0.19/0.41  # Paramodulations                      : 1044
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 17
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 202
% 0.19/0.41  #    Positive orientable unit clauses  : 10
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 3
% 0.19/0.41  #    Non-unit-clauses                  : 189
% 0.19/0.41  # Current number of unprocessed clauses: 677
% 0.19/0.41  # ...number of literals in the above   : 2575
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 45
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 6616
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 3982
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 183
% 0.19/0.41  # Unit Clause-clause subsumption calls : 136
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 6
% 0.19/0.41  # BW rewrite match successes           : 4
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 19580
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.060 s
% 0.19/0.41  # System time              : 0.007 s
% 0.19/0.41  # Total time               : 0.067 s
% 0.19/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
