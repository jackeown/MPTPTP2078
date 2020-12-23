%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0963+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  154 (3958 expanded)
%              Number of clauses        :  122 (1905 expanded)
%              Number of leaves         :   16 (1018 expanded)
%              Depth                    :   24
%              Number of atoms          :  446 (14049 expanded)
%              Number of equality atoms :   88 (1574 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(t5_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( k1_relat_1(X3) = X1
          & ! [X4] :
              ( r2_hidden(X4,X1)
             => r2_hidden(k1_funct_1(X3,X4),X2) ) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

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

fof(c_0_16,plain,(
    ! [X5,X6,X7] :
      ( ~ v1_xboole_0(X5)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
      | v1_xboole_0(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_17,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X40,k1_zfmisc_1(X41))
        | r1_tarski(X40,X41) )
      & ( ~ r1_tarski(X40,X41)
        | m1_subset_1(X40,k1_zfmisc_1(X41)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_18,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk1_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk1_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_19,plain,(
    ! [X17,X18,X19,X21,X22,X23,X25] :
      ( ( r2_hidden(esk2_3(X17,X18,X19),k1_relat_1(X17))
        | ~ r2_hidden(X19,X18)
        | X18 != k2_relat_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( X19 = k1_funct_1(X17,esk2_3(X17,X18,X19))
        | ~ r2_hidden(X19,X18)
        | X18 != k2_relat_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(X22,k1_relat_1(X17))
        | X21 != k1_funct_1(X17,X22)
        | r2_hidden(X21,X18)
        | X18 != k2_relat_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(esk3_2(X17,X23),X23)
        | ~ r2_hidden(X25,k1_relat_1(X17))
        | esk3_2(X17,X23) != k1_funct_1(X17,X25)
        | X23 = k2_relat_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk4_2(X17,X23),k1_relat_1(X17))
        | r2_hidden(esk3_2(X17,X23),X23)
        | X23 = k2_relat_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( esk3_2(X17,X23) = k1_funct_1(X17,esk4_2(X17,X23))
        | r2_hidden(esk3_2(X17,X23),X23)
        | X23 = k2_relat_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( k1_relat_1(X3) = X1
            & ! [X4] :
                ( r2_hidden(X4,X1)
               => r2_hidden(k1_funct_1(X3,X4),X2) ) )
         => ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_funct_2])).

fof(c_0_21,plain,(
    ! [X42,X43,X44] :
      ( ~ r2_hidden(X42,X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(X44))
      | ~ v1_xboole_0(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_22,plain,(
    ! [X30] : m1_subset_1(esk5_1(X30),X30) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_23,plain,(
    ! [X48,X49] :
      ( ~ v1_xboole_0(X48)
      | X48 = X49
      | ~ v1_xboole_0(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,negated_conjecture,(
    ! [X53] :
      ( v1_relat_1(esk8_0)
      & v1_funct_1(esk8_0)
      & k1_relat_1(esk8_0) = esk6_0
      & ( ~ r2_hidden(X53,esk6_0)
        | r2_hidden(k1_funct_1(esk8_0,X53),esk7_0) )
      & ( ~ v1_funct_1(esk8_0)
        | ~ v1_funct_2(esk8_0,esk6_0,esk7_0)
        | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X46,X47] :
      ( ~ r2_hidden(X46,X47)
      | ~ v1_xboole_0(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,esk5_1(k1_zfmisc_1(X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_42,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_relset_1(X32,X33,X34) = k1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,X1),esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,k2_relat_1(esk8_0),X1),esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_48,plain,
    ( r1_tarski(esk5_1(k1_zfmisc_1(X1)),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_49,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X1,X2) = o_0_0_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk8_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_47])).

cnf(c_0_53,plain,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_48])).

fof(c_0_54,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | m1_subset_1(k1_relset_1(X27,X28,X29),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_55,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_27])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,o_0_0_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk8_0),X1)
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_27])).

cnf(c_0_59,plain,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_34])).

cnf(c_0_60,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k1_relset_1(X1,X2,esk6_0) = k1_relat_1(esk6_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_62,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ r1_tarski(k1_relat_1(X37),X35)
      | ~ r1_tarski(k2_relat_1(X37),X36)
      | m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk8_0))
    | ~ v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,plain,
    ( esk5_1(k1_zfmisc_1(X1)) = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk6_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk8_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_34])).

cnf(c_0_68,plain,
    ( r1_tarski(o_0_0_xboole_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk6_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_51])).

cnf(c_0_70,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k2_relat_1(esk8_0) = o_0_0_xboole_0
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_67])).

cnf(c_0_72,plain,
    ( r1_tarski(o_0_0_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_34])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_27])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_51])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk6_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_34])).

cnf(c_0_76,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_40]),c_0_72]),c_0_38])]),c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk6_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,plain,
    ( X1 = k2_zfmisc_1(X2,X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_46])).

cnf(c_0_79,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_34])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk6_0))
    | ~ v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_25]),c_0_56])).

cnf(c_0_81,plain,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_31])).

cnf(c_0_82,negated_conjecture,
    ( k2_zfmisc_1(X1,X2) = esk8_0
    | ~ v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk6_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_34])).

fof(c_0_84,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X38,X39)
      | v1_xboole_0(X39)
      | r2_hidden(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(esk8_0)))
    | ~ v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k2_zfmisc_1(X1,X2) = k1_relat_1(esk6_0)
    | ~ v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_83])).

cnf(c_0_88,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_89,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_90,plain,
    ( r1_tarski(esk5_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_31])).

cnf(c_0_91,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_92,plain,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_31])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(esk8_0)))
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_79])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(k1_relat_1(esk6_0))))
    | ~ v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ m1_subset_1(X1,esk6_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_88])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk5_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_98,plain,
    ( ~ r2_hidden(X1,k1_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_60])).

cnf(c_0_99,plain,
    ( k1_relset_1(X1,X2,esk5_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k1_relat_1(esk5_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_31])).

cnf(c_0_100,plain,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_34])).

cnf(c_0_101,negated_conjecture,
    ( X1 = esk5_1(k1_zfmisc_1(esk8_0))
    | ~ v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_93])).

cnf(c_0_102,negated_conjecture,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(k1_relat_1(esk6_0))))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_34])).

cnf(c_0_103,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_31])).

cnf(c_0_104,plain,
    ( r2_hidden(esk1_2(esk5_1(k1_zfmisc_1(X1)),X2),X1)
    | r1_tarski(esk5_1(k1_zfmisc_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_96,c_0_27])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_funct_1(esk8_0)
    | ~ v1_funct_2(esk8_0,esk6_0,esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(esk2_3(esk8_0,k2_relat_1(esk8_0),X1),esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_97]),c_0_39]),c_0_40])])).

fof(c_0_107,plain,(
    ! [X45] :
      ( ~ v1_xboole_0(X45)
      | X45 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_108,plain,
    ( ~ r2_hidden(X1,k1_relat_1(esk5_1(k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_31])])).

cnf(c_0_109,plain,
    ( esk5_1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_100])).

cnf(c_0_110,negated_conjecture,
    ( esk5_1(k1_zfmisc_1(k1_relat_1(esk6_0))) = esk5_1(k1_zfmisc_1(esk8_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(esk5_1(k1_zfmisc_1(esk6_0)),X1)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_104])).

cnf(c_0_112,negated_conjecture,
    ( ~ v1_funct_2(esk8_0,esk6_0,esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_39])])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_47])).

fof(c_0_114,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_funct_2(X10,X8,X9)
        | X8 = k1_relset_1(X8,X9,X10)
        | X9 = k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( X8 != k1_relset_1(X8,X9,X10)
        | v1_funct_2(X10,X8,X9)
        | X9 = k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( ~ v1_funct_2(X10,X8,X9)
        | X8 = k1_relset_1(X8,X9,X10)
        | X8 != k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( X8 != k1_relset_1(X8,X9,X10)
        | v1_funct_2(X10,X8,X9)
        | X8 != k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( ~ v1_funct_2(X10,X8,X9)
        | X10 = k1_xboole_0
        | X8 = k1_xboole_0
        | X9 != k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( X10 != k1_xboole_0
        | v1_funct_2(X10,X8,X9)
        | X8 = k1_xboole_0
        | X9 != k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_115,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_116,plain,
    ( ~ r2_hidden(X1,k1_relat_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_51]),c_0_109])).

cnf(c_0_117,negated_conjecture,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(esk8_0)))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_110])).

cnf(c_0_118,negated_conjecture,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(esk6_0)))
    | ~ v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_111])).

cnf(c_0_119,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk8_0),esk7_0)
    | ~ r1_tarski(esk6_0,esk6_0)
    | ~ v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_66]),c_0_40]),c_0_38])])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk8_0),X1),esk7_0)
    | r1_tarski(k2_relat_1(esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_27])).

cnf(c_0_121,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_122,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_115,c_0_34])).

cnf(c_0_123,plain,
    ( r1_tarski(k1_relat_1(o_0_0_xboole_0),X1)
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_116,c_0_27])).

cnf(c_0_124,negated_conjecture,
    ( X1 = esk5_1(k1_zfmisc_1(esk8_0))
    | ~ v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_117])).

cnf(c_0_125,negated_conjecture,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(esk6_0)))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_102])).

cnf(c_0_126,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk8_0),esk7_0)
    | ~ v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_36])])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_120])).

cnf(c_0_128,plain,
    ( X1 = o_0_0_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(rw,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_129,plain,
    ( r1_tarski(k1_relat_1(o_0_0_xboole_0),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_123,c_0_34])).

cnf(c_0_130,negated_conjecture,
    ( esk5_1(k1_zfmisc_1(esk8_0)) = esk8_0
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_79])).

cnf(c_0_131,negated_conjecture,
    ( esk5_1(k1_zfmisc_1(esk8_0)) = esk5_1(k1_zfmisc_1(esk6_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_132,negated_conjecture,
    ( ~ v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_127])])).

cnf(c_0_133,plain,
    ( X1 = o_0_0_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),X1)
    | ~ r1_tarski(k1_relat_1(X2),X3) ),
    inference(spm,[status(thm)],[c_0_128,c_0_66])).

cnf(c_0_134,plain,
    ( r1_tarski(k1_relat_1(o_0_0_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_129,c_0_34])).

cnf(c_0_135,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_136,negated_conjecture,
    ( esk5_1(k1_zfmisc_1(esk6_0)) = o_0_0_xboole_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_125])).

cnf(c_0_137,negated_conjecture,
    ( esk5_1(k1_zfmisc_1(esk6_0)) = esk8_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_103])).

cnf(c_0_138,negated_conjecture,
    ( esk7_0 = o_0_0_xboole_0
    | k1_relset_1(esk6_0,esk7_0,esk8_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_40]),c_0_127]),c_0_38]),c_0_36])])).

cnf(c_0_139,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(k2_relat_1(X3),X2)
    | ~ r1_tarski(k1_relat_1(X3),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_66])).

cnf(c_0_140,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_134])).

cnf(c_0_141,plain,
    ( v1_funct_2(X1,o_0_0_xboole_0,X2)
    | k1_relset_1(o_0_0_xboole_0,X2,X1) != o_0_0_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_135]),c_0_122]),c_0_122]),c_0_122]),c_0_122])).

cnf(c_0_142,negated_conjecture,
    ( esk8_0 = o_0_0_xboole_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_143,negated_conjecture,
    ( esk7_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_38]),c_0_40]),c_0_127]),c_0_38]),c_0_36])])).

cnf(c_0_144,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_140,c_0_34])).

cnf(c_0_145,plain,
    ( v1_funct_2(X1,o_0_0_xboole_0,X2)
    | k1_relset_1(o_0_0_xboole_0,X2,X1) != o_0_0_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(o_0_0_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_25])).

cnf(c_0_146,plain,
    ( k1_relset_1(X1,X2,o_0_0_xboole_0) = k1_relat_1(o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_72])).

cnf(c_0_147,negated_conjecture,
    ( esk8_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_143]),c_0_34])])).

cnf(c_0_148,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_144])).

cnf(c_0_149,plain,
    ( v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X1)
    | k1_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_72]),c_0_146])).

cnf(c_0_150,negated_conjecture,
    ( ~ v1_funct_2(o_0_0_xboole_0,esk6_0,o_0_0_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_143]),c_0_147])).

cnf(c_0_151,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_147]),c_0_148])).

cnf(c_0_152,plain,
    ( v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_149,c_0_148])])).

cnf(c_0_153,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_150,c_0_151]),c_0_152])]),
    [proof]).

%------------------------------------------------------------------------------
