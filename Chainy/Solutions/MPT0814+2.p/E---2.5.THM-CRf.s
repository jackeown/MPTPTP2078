%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0814+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:53 EST 2020

% Result     : Theorem 9.34s
% Output     : CNFRefutation 9.34s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 146 expanded)
%              Number of clauses        :   34 (  62 expanded)
%              Number of leaves         :   12 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  181 ( 467 expanded)
%              Number of equality atoms :   26 (  73 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',l3_subset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(d11_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( v1_relat_1(X3)
         => ( X3 = k7_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X4,X2)
                  & r2_hidden(k4_tarski(X4,X5),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',d11_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',dt_k7_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t209_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',d19_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',d5_relat_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',l139_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t3_subset)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
       => ~ ( r2_hidden(X1,X4)
            & ! [X5,X6] :
                ~ ( X1 = k4_tarski(X5,X6)
                  & r2_hidden(X5,X2)
                  & r2_hidden(X6,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_relset_1])).

fof(c_0_13,plain,(
    ! [X316,X317,X318] :
      ( ~ m1_subset_1(X317,k1_zfmisc_1(X316))
      | ~ r2_hidden(X318,X317)
      | r2_hidden(X318,X316) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_14,negated_conjecture,(
    ! [X17,X18] :
      ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & r2_hidden(esk1_0,esk4_0)
      & ( esk1_0 != k4_tarski(X17,X18)
        | ~ r2_hidden(X17,esk2_0)
        | ~ r2_hidden(X18,esk3_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X987,X988,X989] :
      ( ( v4_relat_1(X989,X987)
        | ~ m1_subset_1(X989,k1_zfmisc_1(k2_zfmisc_1(X987,X988))) )
      & ( v5_relat_1(X989,X988)
        | ~ m1_subset_1(X989,k1_zfmisc_1(k2_zfmisc_1(X987,X988))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_16,plain,(
    ! [X851,X852] :
      ( ~ v1_relat_1(X851)
      | ~ m1_subset_1(X852,k1_zfmisc_1(X851))
      | v1_relat_1(X852) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_17,plain,(
    ! [X971,X972] : v1_relat_1(k2_zfmisc_1(X971,X972)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X359,X360,X361,X362,X363,X364,X365] :
      ( ( r2_hidden(X362,X360)
        | ~ r2_hidden(k4_tarski(X362,X363),X361)
        | X361 != k7_relat_1(X359,X360)
        | ~ v1_relat_1(X361)
        | ~ v1_relat_1(X359) )
      & ( r2_hidden(k4_tarski(X362,X363),X359)
        | ~ r2_hidden(k4_tarski(X362,X363),X361)
        | X361 != k7_relat_1(X359,X360)
        | ~ v1_relat_1(X361)
        | ~ v1_relat_1(X359) )
      & ( ~ r2_hidden(X364,X360)
        | ~ r2_hidden(k4_tarski(X364,X365),X359)
        | r2_hidden(k4_tarski(X364,X365),X361)
        | X361 != k7_relat_1(X359,X360)
        | ~ v1_relat_1(X361)
        | ~ v1_relat_1(X359) )
      & ( ~ r2_hidden(k4_tarski(esk48_3(X359,X360,X361),esk49_3(X359,X360,X361)),X361)
        | ~ r2_hidden(esk48_3(X359,X360,X361),X360)
        | ~ r2_hidden(k4_tarski(esk48_3(X359,X360,X361),esk49_3(X359,X360,X361)),X359)
        | X361 = k7_relat_1(X359,X360)
        | ~ v1_relat_1(X361)
        | ~ v1_relat_1(X359) )
      & ( r2_hidden(esk48_3(X359,X360,X361),X360)
        | r2_hidden(k4_tarski(esk48_3(X359,X360,X361),esk49_3(X359,X360,X361)),X361)
        | X361 = k7_relat_1(X359,X360)
        | ~ v1_relat_1(X361)
        | ~ v1_relat_1(X359) )
      & ( r2_hidden(k4_tarski(esk48_3(X359,X360,X361),esk49_3(X359,X360,X361)),X359)
        | r2_hidden(k4_tarski(esk48_3(X359,X360,X361),esk49_3(X359,X360,X361)),X361)
        | X361 = k7_relat_1(X359,X360)
        | ~ v1_relat_1(X361)
        | ~ v1_relat_1(X359) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_21,plain,(
    ! [X1914,X1915] :
      ( ~ v1_relat_1(X1914)
      | v1_relat_1(k7_relat_1(X1914,X1915)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_22,plain,(
    ! [X1939,X1940] :
      ( ~ v1_relat_1(X1940)
      | ~ v4_relat_1(X1940,X1939)
      | X1940 = k7_relat_1(X1940,X1939) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_23,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X2107,X2108] :
      ( ( ~ v5_relat_1(X2108,X2107)
        | r1_tarski(k2_relat_1(X2108),X2107)
        | ~ v1_relat_1(X2108) )
      & ( ~ r1_tarski(k2_relat_1(X2108),X2107)
        | v5_relat_1(X2108,X2107)
        | ~ v1_relat_1(X2108) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_27,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X426,X427,X428,X430,X431,X432,X433,X435] :
      ( ( ~ r2_hidden(X428,X427)
        | r2_hidden(k4_tarski(esk66_3(X426,X427,X428),X428),X426)
        | X427 != k2_relat_1(X426) )
      & ( ~ r2_hidden(k4_tarski(X431,X430),X426)
        | r2_hidden(X430,X427)
        | X427 != k2_relat_1(X426) )
      & ( ~ r2_hidden(esk67_2(X432,X433),X433)
        | ~ r2_hidden(k4_tarski(X435,esk67_2(X432,X433)),X432)
        | X433 = k2_relat_1(X432) )
      & ( r2_hidden(esk67_2(X432,X433),X433)
        | r2_hidden(k4_tarski(esk68_2(X432,X433),esk67_2(X432,X433)),X432)
        | X433 = k2_relat_1(X432) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_29,plain,(
    ! [X138,X139,X140] :
      ( ~ r2_hidden(X138,k2_zfmisc_1(X139,X140))
      | k4_tarski(esk28_1(X138),esk29_1(X138)) = X138 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k7_relat_1(X5,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_25])])).

fof(c_0_37,plain,(
    ! [X848,X849] :
      ( ( ~ m1_subset_1(X848,k1_zfmisc_1(X849))
        | r1_tarski(X848,X849) )
      & ( ~ r1_tarski(X848,X849)
        | m1_subset_1(X848,k1_zfmisc_1(X849)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( v5_relat_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_40,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k4_tarski(esk28_1(X1),esk29_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X4),k7_relat_1(X3,X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( k7_relat_1(esk4_0,esk2_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_36])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k4_tarski(esk28_1(esk1_0),esk29_1(esk1_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( esk1_0 != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X2,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_36])])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk29_1(esk1_0),k2_relat_1(X1))
    | ~ r2_hidden(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk29_1(esk1_0),esk3_0)
    | ~ r2_hidden(esk28_1(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk28_1(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_48]),c_0_31])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk29_1(esk1_0),k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(esk29_1(esk1_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
