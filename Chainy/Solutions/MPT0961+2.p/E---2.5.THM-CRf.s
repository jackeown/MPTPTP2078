%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0961+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:59 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 279 expanded)
%              Number of clauses        :   36 ( 125 expanded)
%              Number of leaves         :   14 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  178 ( 857 expanded)
%              Number of equality atoms :   61 ( 148 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t21_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t3_subset)).

fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',t13_relset_1)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t100_zfmisc_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t5_subset)).

fof(rc1_funct_2,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2)
      & v1_funct_1(X3)
      & v1_funct_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k1_relset_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t113_zfmisc_1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT012+2.ax',t34_mcart_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',fc1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t60_relat_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_funct_1(X1)
          & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t3_funct_2])).

fof(c_0_15,plain,(
    ! [X352] :
      ( ~ v1_relat_1(X352)
      | r1_tarski(X352,k2_zfmisc_1(k1_relat_1(X352),k2_relat_1(X352))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & ( ~ v1_funct_1(esk1_0)
      | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
      | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X68,X69] :
      ( ( ~ m1_subset_1(X68,k1_zfmisc_1(X69))
        | r1_tarski(X68,X69) )
      & ( ~ r1_tarski(X68,X69)
        | m1_subset_1(X68,k1_zfmisc_1(X69)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X103,X104,X105,X106] :
      ( ~ m1_subset_1(X106,k1_zfmisc_1(k2_zfmisc_1(X103,X105)))
      | ~ r1_tarski(k1_relat_1(X106),X104)
      | m1_subset_1(X106,k1_zfmisc_1(k2_zfmisc_1(X104,X105))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
    ! [X146] : r1_tarski(X146,k1_zfmisc_1(k3_tarski(X146))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X77,X78,X79] :
      ( ~ r2_hidden(X77,X78)
      | ~ m1_subset_1(X78,k1_zfmisc_1(X79))
      | ~ v1_xboole_0(X79) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_27,plain,(
    ! [X914,X915] :
      ( m1_subset_1(esk100_2(X914,X915),k1_zfmisc_1(k2_zfmisc_1(X914,X915)))
      & v1_relat_1(esk100_2(X914,X915))
      & v4_relat_1(esk100_2(X914,X915),X914)
      & v5_relat_1(esk100_2(X914,X915),X915)
      & v1_funct_1(esk100_2(X914,X915))
      & v1_funct_2(esk100_2(X914,X915),X914,X915) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_0))))
    | ~ r1_tarski(k1_relat_1(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X3598,X3599,X3600] :
      ( ~ m1_subset_1(X3600,k1_zfmisc_1(k2_zfmisc_1(X3598,X3599)))
      | k1_relset_1(X3598,X3599,X3600) = k1_relat_1(X3600) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_funct_1(esk1_0)
    | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk100_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X1186] :
      ( X1186 = k1_xboole_0
      | r2_hidden(esk139_1(X1186),X1186) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_36,plain,(
    ! [X233,X234] :
      ( ( k2_zfmisc_1(X233,X234) != k1_xboole_0
        | X233 = k1_xboole_0
        | X234 = k1_xboole_0 )
      & ( X233 != k1_xboole_0
        | k2_zfmisc_1(X233,X234) = k1_xboole_0 )
      & ( X234 != k1_xboole_0
        | k2_zfmisc_1(X233,X234) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(esk1_0))),k2_relat_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_38,plain,(
    ! [X3991,X3993,X3994,X3995,X3996] :
      ( ( r2_hidden(esk389_1(X3991),X3991)
        | X3991 = k1_xboole_0 )
      & ( ~ r2_hidden(X3993,X3991)
        | esk389_1(X3991) != k4_mcart_1(X3993,X3994,X3995,X3996)
        | X3991 = k1_xboole_0 )
      & ( ~ r2_hidden(X3994,X3991)
        | esk389_1(X3991) != k4_mcart_1(X3993,X3994,X3995,X3996)
        | X3991 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

fof(c_0_39,plain,(
    ! [X911,X912,X913] :
      ( ( ~ v1_funct_2(X913,X911,X912)
        | X911 = k1_relset_1(X911,X912,X913)
        | X912 = k1_xboole_0
        | ~ m1_subset_1(X913,k1_zfmisc_1(k2_zfmisc_1(X911,X912))) )
      & ( X911 != k1_relset_1(X911,X912,X913)
        | v1_funct_2(X913,X911,X912)
        | X912 = k1_xboole_0
        | ~ m1_subset_1(X913,k1_zfmisc_1(k2_zfmisc_1(X911,X912))) )
      & ( ~ v1_funct_2(X913,X911,X912)
        | X911 = k1_relset_1(X911,X912,X913)
        | X911 != k1_xboole_0
        | ~ m1_subset_1(X913,k1_zfmisc_1(k2_zfmisc_1(X911,X912))) )
      & ( X911 != k1_relset_1(X911,X912,X913)
        | v1_funct_2(X913,X911,X912)
        | X911 != k1_xboole_0
        | ~ m1_subset_1(X913,k1_zfmisc_1(k2_zfmisc_1(X911,X912))) )
      & ( ~ v1_funct_2(X913,X911,X912)
        | X913 = k1_xboole_0
        | X911 = k1_xboole_0
        | X912 != k1_xboole_0
        | ~ m1_subset_1(X913,k1_zfmisc_1(k2_zfmisc_1(X911,X912))) )
      & ( X913 != k1_xboole_0
        | v1_funct_2(X913,X911,X912)
        | X911 = k1_xboole_0
        | X912 != k1_xboole_0
        | ~ m1_subset_1(X913,k1_zfmisc_1(k2_zfmisc_1(X911,X912))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_40,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,esk100_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk139_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(esk1_0))),k2_relat_1(esk1_0)))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(esk389_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k1_relset_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0),esk1_0) = k1_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_24])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_24])])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( esk100_2(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_54,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(esk1_0))),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_24])]),c_0_49])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( v1_funct_2(esk100_2(X1,X2),X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_58,plain,
    ( esk100_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_59,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_53])])).

cnf(c_0_60,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_61,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_55]),c_0_59]),c_0_59]),c_0_60]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
