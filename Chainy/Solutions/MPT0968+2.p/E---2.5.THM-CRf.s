%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0968+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:59 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 289 expanded)
%              Number of clauses        :   38 ( 114 expanded)
%              Number of leaves         :   16 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  259 (1262 expanded)
%              Number of equality atoms :   91 ( 403 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',cc2_relset_1)).

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

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',d19_relat_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k1_relset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t5_subset)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t113_zfmisc_1)).

fof(t45_ordinal1,axiom,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT009+2.ax',t45_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',fc1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t60_relat_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t11_funct_2])).

fof(c_0_17,plain,(
    ! [X3503,X3504,X3505] :
      ( ( v4_relat_1(X3505,X3503)
        | ~ m1_subset_1(X3505,k1_zfmisc_1(k2_zfmisc_1(X3503,X3504))) )
      & ( v5_relat_1(X3505,X3504)
        | ~ m1_subset_1(X3505,k1_zfmisc_1(k2_zfmisc_1(X3503,X3504))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ~ r2_hidden(esk3_0,k1_funct_2(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X818,X819] :
      ( ~ v1_relat_1(X818)
      | ~ m1_subset_1(X819,k1_zfmisc_1(X818))
      | v1_relat_1(X819) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_20,plain,(
    ! [X949,X950] : v1_relat_1(k2_zfmisc_1(X949,X950)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_21,plain,(
    ! [X2443,X2444] :
      ( ( ~ v5_relat_1(X2444,X2443)
        | r1_tarski(k2_relat_1(X2444),X2443)
        | ~ v1_relat_1(X2444) )
      & ( ~ r1_tarski(k2_relat_1(X2444),X2443)
        | v5_relat_1(X2444,X2443)
        | ~ v1_relat_1(X2444) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_22,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X1044,X1045] :
      ( ( v1_funct_1(X1045)
        | ~ r1_tarski(k2_relat_1(X1045),X1044)
        | ~ v1_relat_1(X1045)
        | ~ v1_funct_1(X1045) )
      & ( v1_funct_2(X1045,k1_relat_1(X1045),X1044)
        | ~ r1_tarski(k2_relat_1(X1045),X1044)
        | ~ v1_relat_1(X1045)
        | ~ v1_funct_1(X1045) )
      & ( m1_subset_1(X1045,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1045),X1044)))
        | ~ r1_tarski(k2_relat_1(X1045),X1044)
        | ~ v1_relat_1(X1045)
        | ~ v1_funct_1(X1045) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_25])])).

fof(c_0_30,plain,(
    ! [X632,X633,X634,X635,X637,X638,X639,X640,X641,X643] :
      ( ( v1_relat_1(esk117_4(X632,X633,X634,X635))
        | ~ r2_hidden(X635,X634)
        | X634 != k1_funct_2(X632,X633) )
      & ( v1_funct_1(esk117_4(X632,X633,X634,X635))
        | ~ r2_hidden(X635,X634)
        | X634 != k1_funct_2(X632,X633) )
      & ( X635 = esk117_4(X632,X633,X634,X635)
        | ~ r2_hidden(X635,X634)
        | X634 != k1_funct_2(X632,X633) )
      & ( k1_relat_1(esk117_4(X632,X633,X634,X635)) = X632
        | ~ r2_hidden(X635,X634)
        | X634 != k1_funct_2(X632,X633) )
      & ( r1_tarski(k2_relat_1(esk117_4(X632,X633,X634,X635)),X633)
        | ~ r2_hidden(X635,X634)
        | X634 != k1_funct_2(X632,X633) )
      & ( ~ v1_relat_1(X638)
        | ~ v1_funct_1(X638)
        | X637 != X638
        | k1_relat_1(X638) != X632
        | ~ r1_tarski(k2_relat_1(X638),X633)
        | r2_hidden(X637,X634)
        | X634 != k1_funct_2(X632,X633) )
      & ( ~ r2_hidden(esk118_3(X639,X640,X641),X641)
        | ~ v1_relat_1(X643)
        | ~ v1_funct_1(X643)
        | esk118_3(X639,X640,X641) != X643
        | k1_relat_1(X643) != X639
        | ~ r1_tarski(k2_relat_1(X643),X640)
        | X641 = k1_funct_2(X639,X640) )
      & ( v1_relat_1(esk119_3(X639,X640,X641))
        | r2_hidden(esk118_3(X639,X640,X641),X641)
        | X641 = k1_funct_2(X639,X640) )
      & ( v1_funct_1(esk119_3(X639,X640,X641))
        | r2_hidden(esk118_3(X639,X640,X641),X641)
        | X641 = k1_funct_2(X639,X640) )
      & ( esk118_3(X639,X640,X641) = esk119_3(X639,X640,X641)
        | r2_hidden(esk118_3(X639,X640,X641),X641)
        | X641 = k1_funct_2(X639,X640) )
      & ( k1_relat_1(esk119_3(X639,X640,X641)) = X639
        | r2_hidden(esk118_3(X639,X640,X641),X641)
        | X641 = k1_funct_2(X639,X640) )
      & ( r1_tarski(k2_relat_1(esk119_3(X639,X640,X641)),X640)
        | r2_hidden(esk118_3(X639,X640,X641),X641)
        | X641 = k1_funct_2(X639,X640) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_31,plain,(
    ! [X3445,X3446,X3447] :
      ( ~ m1_subset_1(X3447,k1_zfmisc_1(k2_zfmisc_1(X3445,X3446)))
      | k1_relset_1(X3445,X3446,X3447) = k1_relat_1(X3447) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_32,plain,(
    ! [X353,X354,X355] :
      ( ~ r2_hidden(X353,X354)
      | ~ m1_subset_1(X354,k1_zfmisc_1(X355))
      | ~ v1_xboole_0(X355) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( r2_hidden(X2,X5)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X2 != X1
    | k1_relat_1(X1) != X3
    | ~ r1_tarski(k2_relat_1(X1),X4)
    | X5 != k1_funct_2(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X1037,X1038,X1039] :
      ( ( ~ v1_funct_2(X1039,X1037,X1038)
        | X1037 = k1_relset_1(X1037,X1038,X1039)
        | X1038 = k1_xboole_0
        | ~ m1_subset_1(X1039,k1_zfmisc_1(k2_zfmisc_1(X1037,X1038))) )
      & ( X1037 != k1_relset_1(X1037,X1038,X1039)
        | v1_funct_2(X1039,X1037,X1038)
        | X1038 = k1_xboole_0
        | ~ m1_subset_1(X1039,k1_zfmisc_1(k2_zfmisc_1(X1037,X1038))) )
      & ( ~ v1_funct_2(X1039,X1037,X1038)
        | X1037 = k1_relset_1(X1037,X1038,X1039)
        | X1037 != k1_xboole_0
        | ~ m1_subset_1(X1039,k1_zfmisc_1(k2_zfmisc_1(X1037,X1038))) )
      & ( X1037 != k1_relset_1(X1037,X1038,X1039)
        | v1_funct_2(X1039,X1037,X1038)
        | X1037 != k1_xboole_0
        | ~ m1_subset_1(X1039,k1_zfmisc_1(k2_zfmisc_1(X1037,X1038))) )
      & ( ~ v1_funct_2(X1039,X1037,X1038)
        | X1039 = k1_xboole_0
        | X1037 = k1_xboole_0
        | X1038 != k1_xboole_0
        | ~ m1_subset_1(X1039,k1_zfmisc_1(k2_zfmisc_1(X1037,X1038))) )
      & ( X1039 != k1_xboole_0
        | v1_funct_2(X1039,X1037,X1038)
        | X1037 = k1_xboole_0
        | X1038 != k1_xboole_0
        | ~ m1_subset_1(X1039,k1_zfmisc_1(k2_zfmisc_1(X1037,X1038))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_38,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_29])])).

fof(c_0_41,plain,(
    ! [X4102,X4104,X4105,X4106,X4107] :
      ( ( r2_hidden(esk401_1(X4102),X4102)
        | X4102 = k1_xboole_0 )
      & ( ~ r2_hidden(X4104,X4102)
        | esk401_1(X4102) != k4_mcart_1(X4104,X4105,X4106,X4107)
        | X4102 = k1_xboole_0 )
      & ( ~ r2_hidden(X4105,X4102)
        | esk401_1(X4102) != k4_mcart_1(X4104,X4105,X4106,X4107)
        | X4102 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_funct_2(k1_relat_1(X1),X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])])).

cnf(c_0_43,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_23])).

fof(c_0_46,plain,(
    ! [X675,X676] :
      ( ( k2_zfmisc_1(X675,X676) != k1_xboole_0
        | X675 = k1_xboole_0
        | X676 = k1_xboole_0 )
      & ( X675 != k1_xboole_0
        | k2_zfmisc_1(X675,X676) = k1_xboole_0 )
      & ( X676 != k1_xboole_0
        | k2_zfmisc_1(X675,X676) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( r2_hidden(esk401_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_0,k1_funct_2(k1_relat_1(esk3_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_34]),c_0_35]),c_0_29])])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_23])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_funct_2(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_53,plain,(
    ! [X3493] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X3493)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[t45_ordinal1])).

fof(c_0_54,plain,(
    ! [X654] : r1_tarski(k1_xboole_0,X654) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_55,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_59,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_61,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_62,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])])).

cnf(c_0_66,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_56])])).

cnf(c_0_67,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_56]),c_0_65]),c_0_66]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
