%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:37 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   49 (  99 expanded)
%              Number of clauses        :   29 (  37 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  171 ( 473 expanded)
%              Number of equality atoms :   48 (  90 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t176_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => k7_partfun1(X2,X3,X4) = k3_funct_2(X1,X2,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(d8_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => k7_partfun1(X1,X2,X3) = k1_funct_1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => k7_partfun1(X2,X3,X4) = k3_funct_2(X1,X2,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t176_funct_2])).

fof(c_0_11,plain,(
    ! [X42,X43,X44] :
      ( ( ~ v1_funct_2(X44,X42,X43)
        | X42 = k1_relset_1(X42,X43,X44)
        | X43 = k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X42 != k1_relset_1(X42,X43,X44)
        | v1_funct_2(X44,X42,X43)
        | X43 = k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( ~ v1_funct_2(X44,X42,X43)
        | X42 = k1_relset_1(X42,X43,X44)
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X42 != k1_relset_1(X42,X43,X44)
        | v1_funct_2(X44,X42,X43)
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( ~ v1_funct_2(X44,X42,X43)
        | X44 = k1_xboole_0
        | X42 = k1_xboole_0
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X44 != k1_xboole_0
        | v1_funct_2(X44,X42,X43)
        | X42 = k1_xboole_0
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & m1_subset_1(esk6_0,esk3_0)
    & k7_partfun1(esk4_0,esk5_0,esk6_0) != k3_funct_2(esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k1_relset_1(X36,X37,X38) = k1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_14,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | v1_relat_1(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_19,plain,(
    ! [X23,X24] : v1_relat_1(k2_zfmisc_1(X23,X24)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_20,plain,(
    ! [X48,X49,X50,X51] :
      ( v1_xboole_0(X48)
      | ~ v1_funct_1(X50)
      | ~ v1_funct_2(X50,X48,X49)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | ~ m1_subset_1(X51,X48)
      | k3_funct_2(X48,X49,X50,X51) = k1_funct_1(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_21,plain,(
    ! [X45,X46,X47] :
      ( ~ v1_relat_1(X46)
      | ~ v5_relat_1(X46,X45)
      | ~ v1_funct_1(X46)
      | ~ r2_hidden(X47,k1_relat_1(X46))
      | k7_partfun1(X45,X46,X47) = k1_funct_1(X46,X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_22,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_23,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_24,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
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

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_25])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_35,plain,(
    ! [X33,X34,X35] :
      ( ( v4_relat_1(X35,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( v5_relat_1(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_36,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,X1) = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_28]),c_0_16])]),c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k7_partfun1(X1,esk5_0,X2) = k1_funct_1(esk5_0,X2)
    | esk4_0 = k1_xboole_0
    | ~ v5_relat_1(esk5_0,X1)
    | ~ r2_hidden(X2,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_28]),c_0_32])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_29])).

cnf(c_0_39,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k7_partfun1(esk4_0,esk5_0,esk6_0) != k3_funct_2(esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk6_0) = k1_funct_1(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k7_partfun1(X1,esk5_0,esk6_0) = k1_funct_1(esk5_0,esk6_0)
    | esk4_0 = k1_xboole_0
    | ~ v5_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( v5_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( k7_partfun1(esk4_0,esk5_0,esk6_0) != k1_funct_1(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n019.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:07:22 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.18/0.36  # and selection function SelectCQArNTNpEqFirst.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.023 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t176_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,X1)=>k7_partfun1(X2,X3,X4)=k3_funct_2(X1,X2,X3,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 0.18/0.36  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.18/0.36  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.18/0.36  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.18/0.36  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.18/0.36  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.18/0.36  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 0.18/0.36  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.18/0.36  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.18/0.36  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.36  fof(c_0_10, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,X1)=>k7_partfun1(X2,X3,X4)=k3_funct_2(X1,X2,X3,X4)))))), inference(assume_negation,[status(cth)],[t176_funct_2])).
% 0.18/0.36  fof(c_0_11, plain, ![X42, X43, X44]:((((~v1_funct_2(X44,X42,X43)|X42=k1_relset_1(X42,X43,X44)|X43=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X42!=k1_relset_1(X42,X43,X44)|v1_funct_2(X44,X42,X43)|X43=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))&((~v1_funct_2(X44,X42,X43)|X42=k1_relset_1(X42,X43,X44)|X42!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X42!=k1_relset_1(X42,X43,X44)|v1_funct_2(X44,X42,X43)|X42!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))))&((~v1_funct_2(X44,X42,X43)|X44=k1_xboole_0|X42=k1_xboole_0|X43!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X44!=k1_xboole_0|v1_funct_2(X44,X42,X43)|X42=k1_xboole_0|X43!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.18/0.36  fof(c_0_12, negated_conjecture, (~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(m1_subset_1(esk6_0,esk3_0)&k7_partfun1(esk4_0,esk5_0,esk6_0)!=k3_funct_2(esk3_0,esk4_0,esk5_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.18/0.36  fof(c_0_13, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k1_relset_1(X36,X37,X38)=k1_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.18/0.36  cnf(c_0_14, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.36  cnf(c_0_15, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_17, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  fof(c_0_18, plain, ![X18, X19]:(~v1_relat_1(X18)|(~m1_subset_1(X19,k1_zfmisc_1(X18))|v1_relat_1(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.18/0.36  fof(c_0_19, plain, ![X23, X24]:v1_relat_1(k2_zfmisc_1(X23,X24)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.18/0.36  fof(c_0_20, plain, ![X48, X49, X50, X51]:(v1_xboole_0(X48)|~v1_funct_1(X50)|~v1_funct_2(X50,X48,X49)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|~m1_subset_1(X51,X48)|k3_funct_2(X48,X49,X50,X51)=k1_funct_1(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.18/0.36  fof(c_0_21, plain, ![X45, X46, X47]:(~v1_relat_1(X46)|~v5_relat_1(X46,X45)|~v1_funct_1(X46)|(~r2_hidden(X47,k1_relat_1(X46))|k7_partfun1(X45,X46,X47)=k1_funct_1(X46,X47))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.18/0.36  cnf(c_0_22, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.18/0.36  cnf(c_0_23, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_16])).
% 0.18/0.36  cnf(c_0_24, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.36  cnf(c_0_25, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  fof(c_0_26, plain, ![X15, X16]:(((~m1_subset_1(X16,X15)|r2_hidden(X16,X15)|v1_xboole_0(X15))&(~r2_hidden(X16,X15)|m1_subset_1(X16,X15)|v1_xboole_0(X15)))&((~m1_subset_1(X16,X15)|v1_xboole_0(X16)|~v1_xboole_0(X15))&(~v1_xboole_0(X16)|m1_subset_1(X16,X15)|~v1_xboole_0(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.18/0.36  cnf(c_0_27, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.36  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_29, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_30, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.36  cnf(c_0_31, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.36  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_16]), c_0_25])])).
% 0.18/0.36  cnf(c_0_33, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.36  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  fof(c_0_35, plain, ![X33, X34, X35]:((v4_relat_1(X35,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(v5_relat_1(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.18/0.36  cnf(c_0_36, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,X1)=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_15]), c_0_28]), c_0_16])]), c_0_29])).
% 0.18/0.36  cnf(c_0_37, negated_conjecture, (k7_partfun1(X1,esk5_0,X2)=k1_funct_1(esk5_0,X2)|esk4_0=k1_xboole_0|~v5_relat_1(esk5_0,X1)|~r2_hidden(X2,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_28]), c_0_32])])).
% 0.18/0.36  cnf(c_0_38, negated_conjecture, (r2_hidden(esk6_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_29])).
% 0.18/0.36  cnf(c_0_39, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.36  cnf(c_0_40, negated_conjecture, (k7_partfun1(esk4_0,esk5_0,esk6_0)!=k3_funct_2(esk3_0,esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_41, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk6_0)=k1_funct_1(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.18/0.36  cnf(c_0_42, negated_conjecture, (k7_partfun1(X1,esk5_0,esk6_0)=k1_funct_1(esk5_0,esk6_0)|esk4_0=k1_xboole_0|~v5_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.36  cnf(c_0_43, negated_conjecture, (v5_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_16])).
% 0.18/0.36  cnf(c_0_44, negated_conjecture, (k7_partfun1(esk4_0,esk5_0,esk6_0)!=k1_funct_1(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.36  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_46, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.18/0.36  cnf(c_0_47, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.36  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47])]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 49
% 0.18/0.36  # Proof object clause steps            : 29
% 0.18/0.36  # Proof object formula steps           : 20
% 0.18/0.36  # Proof object conjectures             : 23
% 0.18/0.36  # Proof object clause conjectures      : 20
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 16
% 0.18/0.36  # Proof object initial formulas used   : 10
% 0.18/0.36  # Proof object generating inferences   : 11
% 0.18/0.36  # Proof object simplifying inferences  : 17
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 25
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 52
% 0.18/0.36  # Removed in clause preprocessing      : 2
% 0.18/0.36  # Initial clauses in saturation        : 50
% 0.18/0.36  # Processed clauses                    : 239
% 0.18/0.36  # ...of these trivial                  : 2
% 0.18/0.36  # ...subsumed                          : 38
% 0.18/0.36  # ...remaining for further processing  : 199
% 0.18/0.36  # Other redundant clauses eliminated   : 8
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 33
% 0.18/0.36  # Generated clauses                    : 239
% 0.18/0.36  # ...of the previous two non-trivial   : 214
% 0.18/0.36  # Contextual simplify-reflections      : 1
% 0.18/0.36  # Paramodulations                      : 232
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 8
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 109
% 0.18/0.36  #    Positive orientable unit clauses  : 32
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 5
% 0.18/0.36  #    Non-unit-clauses                  : 72
% 0.18/0.36  # Current number of unprocessed clauses: 55
% 0.18/0.36  # ...number of literals in the above   : 129
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 83
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 945
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 619
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 26
% 0.18/0.36  # Unit Clause-clause subsumption calls : 68
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 24
% 0.18/0.36  # BW rewrite match successes           : 3
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 7246
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.033 s
% 0.18/0.36  # System time              : 0.005 s
% 0.18/0.36  # Total time               : 0.037 s
% 0.18/0.36  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
