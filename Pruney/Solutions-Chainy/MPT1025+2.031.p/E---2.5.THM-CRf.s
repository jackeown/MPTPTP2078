%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:39 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 138 expanded)
%              Number of clauses        :   40 (  58 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  253 ( 614 expanded)
%              Number of equality atoms :   58 (  97 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(t116_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ~ ( r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(c_0_14,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | ~ v1_xboole_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_23,plain,(
    ! [X49,X50,X51,X52] :
      ( ( X49 = k4_tarski(esk6_4(X49,X50,X51,X52),esk7_4(X49,X50,X51,X52))
        | ~ r2_hidden(X49,X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( r2_hidden(esk6_4(X49,X50,X51,X52),X50)
        | ~ r2_hidden(X49,X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( r2_hidden(esk7_4(X49,X50,X51,X52),X51)
        | ~ r2_hidden(X49,X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ~ ( r2_hidden(X6,X3)
                      & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_funct_2])).

fof(c_0_25,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k1_relset_1(X42,X43,X44) = k1_relat_1(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_26,plain,(
    ! [X55,X56,X57] :
      ( ( ~ v1_funct_2(X57,X55,X56)
        | X55 = k1_relset_1(X55,X56,X57)
        | X56 = k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( X55 != k1_relset_1(X55,X56,X57)
        | v1_funct_2(X57,X55,X56)
        | X56 = k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( ~ v1_funct_2(X57,X55,X56)
        | X55 = k1_relset_1(X55,X56,X57)
        | X55 != k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( X55 != k1_relset_1(X55,X56,X57)
        | v1_funct_2(X57,X55,X56)
        | X55 != k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( ~ v1_funct_2(X57,X55,X56)
        | X57 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 != k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( X57 != k1_xboole_0
        | v1_funct_2(X57,X55,X56)
        | X55 = k1_xboole_0
        | X56 != k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(esk7_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,negated_conjecture,(
    ! [X63] :
      ( v1_funct_1(esk11_0)
      & v1_funct_2(esk11_0,esk8_0,esk9_0)
      & m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))
      & r2_hidden(esk12_0,k7_relset_1(esk8_0,esk9_0,esk11_0,esk10_0))
      & ( ~ m1_subset_1(X63,esk8_0)
        | ~ r2_hidden(X63,esk10_0)
        | esk12_0 != k1_funct_1(esk11_0,X63) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X3)
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk11_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | v1_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0)
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( esk8_0 = k1_relat_1(esk11_0)
    | esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_33])])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_40,plain,(
    ! [X31,X32,X33,X35] :
      ( ( r2_hidden(esk5_3(X31,X32,X33),k1_relat_1(X33))
        | ~ r2_hidden(X31,k9_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(k4_tarski(esk5_3(X31,X32,X33),X31),X33)
        | ~ r2_hidden(X31,k9_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(esk5_3(X31,X32,X33),X32)
        | ~ r2_hidden(X31,k9_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(X35,k1_relat_1(X33))
        | ~ r2_hidden(k4_tarski(X35,X31),X33)
        | ~ r2_hidden(X35,X32)
        | r2_hidden(X31,k9_relat_1(X33,X32))
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_41,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
    ! [X45,X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | k7_relset_1(X45,X46,X47,X48) = k9_relat_1(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_43,negated_conjecture,
    ( esk8_0 = k1_relat_1(esk11_0)
    | ~ r2_hidden(X1,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk12_0,k7_relset_1(esk8_0,esk9_0,esk11_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( esk8_0 = k1_relat_1(esk11_0)
    | ~ r2_hidden(X1,k9_relat_1(esk11_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk12_0,k9_relat_1(esk11_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_33])])).

fof(c_0_50,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(X36,k1_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( X37 = k1_funct_1(X38,X36)
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( ~ r2_hidden(X36,k1_relat_1(X38))
        | X37 != k1_funct_1(X38,X36)
        | r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(X1,esk8_0)
    | ~ r2_hidden(X1,esk10_0)
    | esk12_0 != k1_funct_1(esk11_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( esk8_0 = k1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( esk12_0 != k1_funct_1(esk11_0,X1)
    | ~ m1_subset_1(X1,k1_relat_1(esk11_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,plain,
    ( k1_funct_1(X1,esk5_3(X2,X3,X1)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_57,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | m1_subset_1(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_58,negated_conjecture,
    ( esk12_0 != X1
    | ~ m1_subset_1(esk5_3(X1,X2,esk11_0),k1_relat_1(esk11_0))
    | ~ r2_hidden(esk5_3(X1,X2,esk11_0),esk10_0)
    | ~ r2_hidden(X1,k9_relat_1(esk11_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_45])])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_60,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k4_tarski(X22,esk2_3(X20,X21,X22)),X20)
        | X21 != k1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X24,X25),X20)
        | r2_hidden(X24,X21)
        | X21 != k1_relat_1(X20) )
      & ( ~ r2_hidden(esk3_2(X26,X27),X27)
        | ~ r2_hidden(k4_tarski(esk3_2(X26,X27),X29),X26)
        | X27 = k1_relat_1(X26) )
      & ( r2_hidden(esk3_2(X26,X27),X27)
        | r2_hidden(k4_tarski(esk3_2(X26,X27),esk4_2(X26,X27)),X26)
        | X27 = k1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_61,negated_conjecture,
    ( esk12_0 != X1
    | ~ r2_hidden(esk5_3(X1,X2,esk11_0),k1_relat_1(esk11_0))
    | ~ r2_hidden(esk5_3(X1,X2,esk11_0),esk10_0)
    | ~ r2_hidden(X1,k9_relat_1(esk11_0,X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( esk12_0 != X1
    | ~ r2_hidden(esk5_3(X1,esk10_0,esk11_0),k1_relat_1(esk11_0))
    | ~ r2_hidden(X1,k9_relat_1(esk11_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_45])])).

cnf(c_0_65,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X4)
    | X4 != k1_relat_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_44])).

cnf(c_0_66,negated_conjecture,
    ( esk12_0 != X1
    | ~ r2_hidden(X1,k9_relat_1(esk11_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_45])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_66,c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:41:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 4.87/5.05  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 4.87/5.05  # and selection function SelectMaxLComplexAvoidPosPred.
% 4.87/5.05  #
% 4.87/5.05  # Preprocessing time       : 0.029 s
% 4.87/5.05  # Presaturation interreduction done
% 4.87/5.05  
% 4.87/5.05  # Proof found!
% 4.87/5.05  # SZS status Theorem
% 4.87/5.05  # SZS output start CNFRefutation
% 4.87/5.05  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.87/5.05  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.87/5.05  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.87/5.05  fof(t6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 4.87/5.05  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 4.87/5.05  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.87/5.05  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.87/5.05  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.87/5.05  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.87/5.05  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.87/5.05  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.87/5.05  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 4.87/5.05  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.87/5.05  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 4.87/5.05  fof(c_0_14, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 4.87/5.05  fof(c_0_15, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 4.87/5.05  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.87/5.05  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.87/5.05  fof(c_0_18, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|~v1_xboole_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 4.87/5.05  cnf(c_0_19, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.87/5.05  cnf(c_0_20, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 4.87/5.05  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.87/5.05  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 4.87/5.05  fof(c_0_23, plain, ![X49, X50, X51, X52]:(((X49=k4_tarski(esk6_4(X49,X50,X51,X52),esk7_4(X49,X50,X51,X52))|~r2_hidden(X49,X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(r2_hidden(esk6_4(X49,X50,X51,X52),X50)|~r2_hidden(X49,X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))&(r2_hidden(esk7_4(X49,X50,X51,X52),X51)|~r2_hidden(X49,X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).
% 4.87/5.05  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 4.87/5.05  fof(c_0_25, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k1_relset_1(X42,X43,X44)=k1_relat_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 4.87/5.05  fof(c_0_26, plain, ![X55, X56, X57]:((((~v1_funct_2(X57,X55,X56)|X55=k1_relset_1(X55,X56,X57)|X56=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X55!=k1_relset_1(X55,X56,X57)|v1_funct_2(X57,X55,X56)|X56=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&((~v1_funct_2(X57,X55,X56)|X55=k1_relset_1(X55,X56,X57)|X55!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X55!=k1_relset_1(X55,X56,X57)|v1_funct_2(X57,X55,X56)|X55!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))))&((~v1_funct_2(X57,X55,X56)|X57=k1_xboole_0|X55=k1_xboole_0|X56!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X57!=k1_xboole_0|v1_funct_2(X57,X55,X56)|X55=k1_xboole_0|X56!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 4.87/5.05  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 4.87/5.05  cnf(c_0_28, plain, (r2_hidden(esk7_4(X1,X2,X3,X4),X3)|~r2_hidden(X1,X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.87/5.05  fof(c_0_29, negated_conjecture, ![X63]:(((v1_funct_1(esk11_0)&v1_funct_2(esk11_0,esk8_0,esk9_0))&m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))))&(r2_hidden(esk12_0,k7_relset_1(esk8_0,esk9_0,esk11_0,esk10_0))&(~m1_subset_1(X63,esk8_0)|(~r2_hidden(X63,esk10_0)|esk12_0!=k1_funct_1(esk11_0,X63))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])])).
% 4.87/5.05  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.87/5.05  cnf(c_0_31, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.87/5.05  cnf(c_0_32, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_xboole_0(X3)|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 4.87/5.05  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.87/5.05  cnf(c_0_34, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 4.87/5.05  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk11_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.87/5.05  fof(c_0_36, plain, ![X39, X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|v1_relat_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 4.87/5.05  cnf(c_0_37, negated_conjecture, (~v1_xboole_0(esk9_0)|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 4.87/5.05  cnf(c_0_38, negated_conjecture, (esk8_0=k1_relat_1(esk11_0)|esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_33])])).
% 4.87/5.05  cnf(c_0_39, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 4.87/5.05  fof(c_0_40, plain, ![X31, X32, X33, X35]:((((r2_hidden(esk5_3(X31,X32,X33),k1_relat_1(X33))|~r2_hidden(X31,k9_relat_1(X33,X32))|~v1_relat_1(X33))&(r2_hidden(k4_tarski(esk5_3(X31,X32,X33),X31),X33)|~r2_hidden(X31,k9_relat_1(X33,X32))|~v1_relat_1(X33)))&(r2_hidden(esk5_3(X31,X32,X33),X32)|~r2_hidden(X31,k9_relat_1(X33,X32))|~v1_relat_1(X33)))&(~r2_hidden(X35,k1_relat_1(X33))|~r2_hidden(k4_tarski(X35,X31),X33)|~r2_hidden(X35,X32)|r2_hidden(X31,k9_relat_1(X33,X32))|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 4.87/5.05  cnf(c_0_41, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 4.87/5.05  fof(c_0_42, plain, ![X45, X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|k7_relset_1(X45,X46,X47,X48)=k9_relat_1(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 4.87/5.05  cnf(c_0_43, negated_conjecture, (esk8_0=k1_relat_1(esk11_0)|~r2_hidden(X1,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 4.87/5.05  cnf(c_0_44, plain, (r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 4.87/5.05  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_41, c_0_33])).
% 4.87/5.05  cnf(c_0_46, negated_conjecture, (r2_hidden(esk12_0,k7_relset_1(esk8_0,esk9_0,esk11_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.87/5.05  cnf(c_0_47, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 4.87/5.05  cnf(c_0_48, negated_conjecture, (esk8_0=k1_relat_1(esk11_0)|~r2_hidden(X1,k9_relat_1(esk11_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 4.87/5.05  cnf(c_0_49, negated_conjecture, (r2_hidden(esk12_0,k9_relat_1(esk11_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_33])])).
% 4.87/5.05  fof(c_0_50, plain, ![X36, X37, X38]:(((r2_hidden(X36,k1_relat_1(X38))|~r2_hidden(k4_tarski(X36,X37),X38)|(~v1_relat_1(X38)|~v1_funct_1(X38)))&(X37=k1_funct_1(X38,X36)|~r2_hidden(k4_tarski(X36,X37),X38)|(~v1_relat_1(X38)|~v1_funct_1(X38))))&(~r2_hidden(X36,k1_relat_1(X38))|X37!=k1_funct_1(X38,X36)|r2_hidden(k4_tarski(X36,X37),X38)|(~v1_relat_1(X38)|~v1_funct_1(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 4.87/5.05  cnf(c_0_51, negated_conjecture, (~m1_subset_1(X1,esk8_0)|~r2_hidden(X1,esk10_0)|esk12_0!=k1_funct_1(esk11_0,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.87/5.05  cnf(c_0_52, negated_conjecture, (esk8_0=k1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 4.87/5.05  cnf(c_0_53, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.87/5.05  cnf(c_0_54, negated_conjecture, (esk12_0!=k1_funct_1(esk11_0,X1)|~m1_subset_1(X1,k1_relat_1(esk11_0))|~r2_hidden(X1,esk10_0)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 4.87/5.05  cnf(c_0_55, plain, (k1_funct_1(X1,esk5_3(X2,X3,X1))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_53, c_0_44])).
% 4.87/5.05  cnf(c_0_56, negated_conjecture, (v1_funct_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.87/5.05  fof(c_0_57, plain, ![X13, X14]:(~r2_hidden(X13,X14)|m1_subset_1(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 4.87/5.05  cnf(c_0_58, negated_conjecture, (esk12_0!=X1|~m1_subset_1(esk5_3(X1,X2,esk11_0),k1_relat_1(esk11_0))|~r2_hidden(esk5_3(X1,X2,esk11_0),esk10_0)|~r2_hidden(X1,k9_relat_1(esk11_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_45])])).
% 4.87/5.05  cnf(c_0_59, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 4.87/5.05  fof(c_0_60, plain, ![X20, X21, X22, X24, X25, X26, X27, X29]:(((~r2_hidden(X22,X21)|r2_hidden(k4_tarski(X22,esk2_3(X20,X21,X22)),X20)|X21!=k1_relat_1(X20))&(~r2_hidden(k4_tarski(X24,X25),X20)|r2_hidden(X24,X21)|X21!=k1_relat_1(X20)))&((~r2_hidden(esk3_2(X26,X27),X27)|~r2_hidden(k4_tarski(esk3_2(X26,X27),X29),X26)|X27=k1_relat_1(X26))&(r2_hidden(esk3_2(X26,X27),X27)|r2_hidden(k4_tarski(esk3_2(X26,X27),esk4_2(X26,X27)),X26)|X27=k1_relat_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 4.87/5.05  cnf(c_0_61, negated_conjecture, (esk12_0!=X1|~r2_hidden(esk5_3(X1,X2,esk11_0),k1_relat_1(esk11_0))|~r2_hidden(esk5_3(X1,X2,esk11_0),esk10_0)|~r2_hidden(X1,k9_relat_1(esk11_0,X2))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 4.87/5.05  cnf(c_0_62, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 4.87/5.05  cnf(c_0_63, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 4.87/5.05  cnf(c_0_64, negated_conjecture, (esk12_0!=X1|~r2_hidden(esk5_3(X1,esk10_0,esk11_0),k1_relat_1(esk11_0))|~r2_hidden(X1,k9_relat_1(esk11_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_45])])).
% 4.87/5.05  cnf(c_0_65, plain, (r2_hidden(esk5_3(X1,X2,X3),X4)|X4!=k1_relat_1(X3)|~v1_relat_1(X3)|~r2_hidden(X1,k9_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_63, c_0_44])).
% 4.87/5.05  cnf(c_0_66, negated_conjecture, (esk12_0!=X1|~r2_hidden(X1,k9_relat_1(esk11_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_45])])).
% 4.87/5.05  cnf(c_0_67, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_66, c_0_49]), ['proof']).
% 4.87/5.05  # SZS output end CNFRefutation
% 4.87/5.05  # Proof object total steps             : 68
% 4.87/5.05  # Proof object clause steps            : 40
% 4.87/5.05  # Proof object formula steps           : 28
% 4.87/5.05  # Proof object conjectures             : 21
% 4.87/5.05  # Proof object clause conjectures      : 18
% 4.87/5.05  # Proof object formula conjectures     : 3
% 4.87/5.05  # Proof object initial clauses used    : 20
% 4.87/5.05  # Proof object initial formulas used   : 14
% 4.87/5.05  # Proof object generating inferences   : 19
% 4.87/5.05  # Proof object simplifying inferences  : 16
% 4.87/5.05  # Training examples: 0 positive, 0 negative
% 4.87/5.05  # Parsed axioms                        : 14
% 4.87/5.05  # Removed by relevancy pruning/SinE    : 0
% 4.87/5.05  # Initial clauses                      : 36
% 4.87/5.05  # Removed in clause preprocessing      : 0
% 4.87/5.05  # Initial clauses in saturation        : 36
% 4.87/5.05  # Processed clauses                    : 32607
% 4.87/5.05  # ...of these trivial                  : 39
% 4.87/5.05  # ...subsumed                          : 28915
% 4.87/5.05  # ...remaining for further processing  : 3653
% 4.87/5.05  # Other redundant clauses eliminated   : 4
% 4.87/5.05  # Clauses deleted for lack of memory   : 0
% 4.87/5.05  # Backward-subsumed                    : 180
% 4.87/5.05  # Backward-rewritten                   : 182
% 4.87/5.05  # Generated clauses                    : 408143
% 4.87/5.05  # ...of the previous two non-trivial   : 397760
% 4.87/5.05  # Contextual simplify-reflections      : 102
% 4.87/5.05  # Paramodulations                      : 407641
% 4.87/5.05  # Factorizations                       : 6
% 4.87/5.05  # Equation resolutions                 : 496
% 4.87/5.05  # Propositional unsat checks           : 0
% 4.87/5.05  #    Propositional check models        : 0
% 4.87/5.05  #    Propositional check unsatisfiable : 0
% 4.87/5.05  #    Propositional clauses             : 0
% 4.87/5.05  #    Propositional clauses after purity: 0
% 4.87/5.05  #    Propositional unsat core size     : 0
% 4.87/5.05  #    Propositional preprocessing time  : 0.000
% 4.87/5.05  #    Propositional encoding time       : 0.000
% 4.87/5.05  #    Propositional solver time         : 0.000
% 4.87/5.05  #    Success case prop preproc time    : 0.000
% 4.87/5.05  #    Success case prop encoding time   : 0.000
% 4.87/5.05  #    Success case prop solver time     : 0.000
% 4.87/5.05  # Current number of processed clauses  : 3255
% 4.87/5.05  #    Positive orientable unit clauses  : 22
% 4.87/5.05  #    Positive unorientable unit clauses: 0
% 4.87/5.05  #    Negative unit clauses             : 13
% 4.87/5.05  #    Non-unit-clauses                  : 3220
% 4.87/5.05  # Current number of unprocessed clauses: 363773
% 4.87/5.05  # ...number of literals in the above   : 2551251
% 4.87/5.05  # Current number of archived formulas  : 0
% 4.87/5.05  # Current number of archived clauses   : 398
% 4.87/5.05  # Clause-clause subsumption calls (NU) : 1241556
% 4.87/5.05  # Rec. Clause-clause subsumption calls : 263644
% 4.87/5.05  # Non-unit clause-clause subsumptions  : 13159
% 4.87/5.05  # Unit Clause-clause subsumption calls : 625
% 4.87/5.05  # Rewrite failures with RHS unbound    : 0
% 4.87/5.05  # BW rewrite match attempts            : 108
% 4.87/5.05  # BW rewrite match successes           : 30
% 4.87/5.05  # Condensation attempts                : 0
% 4.87/5.05  # Condensation successes               : 0
% 4.87/5.05  # Termbank termtop insertions          : 8726064
% 4.87/5.07  
% 4.87/5.07  # -------------------------------------------------
% 4.87/5.07  # User time                : 4.567 s
% 4.87/5.07  # System time              : 0.165 s
% 4.87/5.07  # Total time               : 4.732 s
% 4.87/5.07  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
