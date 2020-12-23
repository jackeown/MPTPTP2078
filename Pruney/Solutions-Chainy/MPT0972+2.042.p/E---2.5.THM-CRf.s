%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:48 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 (3611 expanded)
%              Number of clauses        :   70 (1374 expanded)
%              Number of leaves         :   14 ( 892 expanded)
%              Depth                    :   20
%              Number of atoms          :  291 (20347 expanded)
%              Number of equality atoms :  104 (5032 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( r2_hidden(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(reflexivity_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_relset_1(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( ! [X5] :
                  ( r2_hidden(X5,X1)
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
             => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_2])).

fof(c_0_15,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k1_relset_1(X48,X49,X50) = k1_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_16,negated_conjecture,(
    ! [X62] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk6_0,esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk6_0,esk7_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & ( ~ r2_hidden(X62,esk6_0)
        | k1_funct_1(esk8_0,X62) = k1_funct_1(esk9_0,X62) )
      & ~ r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
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

cnf(c_0_18,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | v1_relat_1(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_21,plain,(
    ! [X38,X39] : v1_relat_1(k2_zfmisc_1(X38,X39)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_22,plain,(
    ! [X40,X41] :
      ( ( r2_hidden(esk5_2(X40,X41),k1_relat_1(X40))
        | k1_relat_1(X40) != k1_relat_1(X41)
        | X40 = X41
        | ~ v1_relat_1(X41)
        | ~ v1_funct_1(X41)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) )
      & ( k1_funct_1(X40,esk5_2(X40,X41)) != k1_funct_1(X41,esk5_2(X40,X41))
        | k1_relat_1(X40) != k1_relat_1(X41)
        | X40 = X41
        | ~ v1_relat_1(X41)
        | ~ v1_funct_1(X41)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_23,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_24]),c_0_25])])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_27])])).

cnf(c_0_33,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = X1
    | r2_hidden(esk5_2(esk8_0,X1),esk6_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_28]),c_0_33]),c_0_34])])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_28]),c_0_27])])).

fof(c_0_39,plain,(
    ! [X14,X15] :
      ( ( k2_zfmisc_1(X14,X15) != k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_40,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk5_2(X1,X2)) != k1_funct_1(X2,esk5_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk8_0,X1) = k1_funct_1(esk9_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( esk8_0 = esk9_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk5_2(esk8_0,esk9_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | X1 = esk9_0
    | k1_funct_1(X1,esk5_2(X1,esk9_0)) != k1_funct_1(esk9_0,esk5_2(X1,esk9_0))
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk8_0,esk5_2(esk8_0,esk9_0)) = k1_funct_1(esk9_0,esk5_2(esk8_0,esk9_0))
    | esk7_0 = k1_xboole_0
    | esk8_0 = esk9_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_46,plain,(
    ! [X51,X52,X53,X54] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | r2_relset_1(X51,X52,X53,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).

fof(c_0_47,plain,(
    ! [X45,X46,X47] :
      ( ( v4_relat_1(X47,X45)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( v5_relat_1(X47,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_48,plain,(
    ! [X19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X19)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( esk8_0 = esk9_0
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_30]),c_0_31]),c_0_32])]),c_0_45])).

cnf(c_0_52,plain,
    ( r2_relset_1(X2,X3,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_53,plain,(
    ! [X25,X26] :
      ( ( ~ v4_relat_1(X26,X25)
        | r1_tarski(k1_relat_1(X26),X25)
        | ~ v1_relat_1(X26) )
      & ( ~ r1_tarski(k1_relat_1(X26),X25)
        | v4_relat_1(X26,X25)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_54,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_49]),c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( esk8_0 = esk9_0
    | v1_funct_2(esk8_0,esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( esk8_0 = esk9_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_51]),c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r2_relset_1(esk6_0,esk7_0,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_28])).

fof(c_0_60,plain,(
    ! [X13] :
      ( ~ r1_tarski(X13,k1_xboole_0)
      | X13 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( esk8_0 = esk9_0
    | esk6_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( r2_relset_1(esk6_0,esk7_0,esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_28])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

fof(c_0_69,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | ~ r2_hidden(X18,X17)
      | r2_hidden(X18,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_70,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_71,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_73,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_74,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_70]),c_0_71])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk6_0,esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_19])).

cnf(c_0_76,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v1_funct_2(esk9_0,esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | m1_subset_1(esk9_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_74]),c_0_50])).

cnf(c_0_79,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_55])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,X1),k2_zfmisc_1(esk6_0,esk7_0))
    | r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ r2_relset_1(esk6_0,esk7_0,k1_xboole_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_70])).

cnf(c_0_83,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_77]),c_0_78])).

cnf(c_0_84,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_55])).

cnf(c_0_85,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk6_0,esk7_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_28])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])])).

cnf(c_0_89,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,X1),k2_zfmisc_1(esk6_0,esk7_0))
    | r1_tarski(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_76])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(esk8_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,esk7_0,esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_64,c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk9_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_88]),c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,esk7_0,k1_xboole_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97]),c_0_84])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:06:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.21/0.39  # and selection function SelectNewComplexAHP.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.029 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t18_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 0.21/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.39  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 0.21/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.39  fof(reflexivity_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_relset_1(X1,X2,X3,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 0.21/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.39  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.21/0.39  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.21/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.21/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.39  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4))))), inference(assume_negation,[status(cth)],[t18_funct_2])).
% 0.21/0.39  fof(c_0_15, plain, ![X48, X49, X50]:(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k1_relset_1(X48,X49,X50)=k1_relat_1(X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.39  fof(c_0_16, negated_conjecture, ![X62]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&((~r2_hidden(X62,esk6_0)|k1_funct_1(esk8_0,X62)=k1_funct_1(esk9_0,X62))&~r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).
% 0.21/0.39  fof(c_0_17, plain, ![X55, X56, X57]:((((~v1_funct_2(X57,X55,X56)|X55=k1_relset_1(X55,X56,X57)|X56=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X55!=k1_relset_1(X55,X56,X57)|v1_funct_2(X57,X55,X56)|X56=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&((~v1_funct_2(X57,X55,X56)|X55=k1_relset_1(X55,X56,X57)|X55!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X55!=k1_relset_1(X55,X56,X57)|v1_funct_2(X57,X55,X56)|X55!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))))&((~v1_funct_2(X57,X55,X56)|X57=k1_xboole_0|X55=k1_xboole_0|X56!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X57!=k1_xboole_0|v1_funct_2(X57,X55,X56)|X55=k1_xboole_0|X56!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.39  cnf(c_0_18, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  fof(c_0_20, plain, ![X23, X24]:(~v1_relat_1(X23)|(~m1_subset_1(X24,k1_zfmisc_1(X23))|v1_relat_1(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.39  fof(c_0_21, plain, ![X38, X39]:v1_relat_1(k2_zfmisc_1(X38,X39)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.39  fof(c_0_22, plain, ![X40, X41]:((r2_hidden(esk5_2(X40,X41),k1_relat_1(X40))|k1_relat_1(X40)!=k1_relat_1(X41)|X40=X41|(~v1_relat_1(X41)|~v1_funct_1(X41))|(~v1_relat_1(X40)|~v1_funct_1(X40)))&(k1_funct_1(X40,esk5_2(X40,X41))!=k1_funct_1(X41,esk5_2(X40,X41))|k1_relat_1(X40)!=k1_relat_1(X41)|X40=X41|(~v1_relat_1(X41)|~v1_funct_1(X41))|(~v1_relat_1(X40)|~v1_funct_1(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.21/0.39  cnf(c_0_23, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_26, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_27, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_29, plain, (r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_30, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_24]), c_0_25])])).
% 0.21/0.39  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_19]), c_0_27])])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_18, c_0_28])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_35, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=X1|r2_hidden(esk5_2(esk8_0,X1),esk6_0)|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])).
% 0.21/0.39  cnf(c_0_36, negated_conjecture, (k1_relat_1(esk9_0)=esk6_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_28]), c_0_33]), c_0_34])])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_28]), c_0_27])])).
% 0.21/0.39  fof(c_0_39, plain, ![X14, X15]:((k2_zfmisc_1(X14,X15)!=k1_xboole_0|(X14=k1_xboole_0|X15=k1_xboole_0))&((X14!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0)&(X15!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.39  cnf(c_0_40, plain, (X1=X2|k1_funct_1(X1,esk5_2(X1,X2))!=k1_funct_1(X2,esk5_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_41, negated_conjecture, (k1_funct_1(esk8_0,X1)=k1_funct_1(esk9_0,X1)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (esk8_0=esk9_0|esk7_0=k1_xboole_0|r2_hidden(esk5_2(esk8_0,esk9_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])])).
% 0.21/0.39  cnf(c_0_43, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.39  cnf(c_0_44, negated_conjecture, (esk7_0=k1_xboole_0|X1=esk9_0|k1_funct_1(X1,esk5_2(X1,esk9_0))!=k1_funct_1(esk9_0,esk5_2(X1,esk9_0))|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_37]), c_0_38])])).
% 0.21/0.39  cnf(c_0_45, negated_conjecture, (k1_funct_1(esk8_0,esk5_2(esk8_0,esk9_0))=k1_funct_1(esk9_0,esk5_2(esk8_0,esk9_0))|esk7_0=k1_xboole_0|esk8_0=esk9_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.39  fof(c_0_46, plain, ![X51, X52, X53, X54]:(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|r2_relset_1(X51,X52,X53,X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).
% 0.21/0.39  fof(c_0_47, plain, ![X45, X46, X47]:((v4_relat_1(X47,X45)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(v5_relat_1(X47,X46)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.39  fof(c_0_48, plain, ![X19]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X19)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.39  cnf(c_0_49, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_50, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_43])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (esk8_0=esk9_0|esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_30]), c_0_31]), c_0_32])]), c_0_45])).
% 0.21/0.39  cnf(c_0_52, plain, (r2_relset_1(X2,X3,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.39  fof(c_0_53, plain, ![X25, X26]:((~v4_relat_1(X26,X25)|r1_tarski(k1_relat_1(X26),X25)|~v1_relat_1(X26))&(~r1_tarski(k1_relat_1(X26),X25)|v4_relat_1(X26,X25)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.21/0.39  cnf(c_0_54, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.39  cnf(c_0_55, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.39  cnf(c_0_56, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_49]), c_0_50])).
% 0.21/0.39  cnf(c_0_57, negated_conjecture, (esk8_0=esk9_0|v1_funct_2(esk8_0,esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_51])).
% 0.21/0.39  cnf(c_0_58, negated_conjecture, (esk8_0=esk9_0|m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_51]), c_0_50])).
% 0.21/0.39  cnf(c_0_59, negated_conjecture, (r2_relset_1(esk6_0,esk7_0,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_52, c_0_28])).
% 0.21/0.39  fof(c_0_60, plain, ![X13]:(~r1_tarski(X13,k1_xboole_0)|X13=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.21/0.39  cnf(c_0_61, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.39  cnf(c_0_62, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.39  cnf(c_0_63, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_50])).
% 0.21/0.39  cnf(c_0_64, negated_conjecture, (~r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_65, negated_conjecture, (esk8_0=esk9_0|esk6_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.21/0.39  cnf(c_0_66, negated_conjecture, (r2_relset_1(esk6_0,esk7_0,esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_59, c_0_28])).
% 0.21/0.39  cnf(c_0_67, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.39  cnf(c_0_68, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])])).
% 0.21/0.39  fof(c_0_69, plain, ![X16, X17, X18]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|(~r2_hidden(X18,X17)|r2_hidden(X18,X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.21/0.39  cnf(c_0_70, negated_conjecture, (esk8_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 0.21/0.39  cnf(c_0_71, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.39  cnf(c_0_72, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.21/0.39  fof(c_0_73, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.39  cnf(c_0_74, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_70]), c_0_71])])).
% 0.21/0.39  cnf(c_0_75, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk6_0,esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_72, c_0_19])).
% 0.21/0.39  cnf(c_0_76, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.21/0.39  cnf(c_0_77, negated_conjecture, (esk6_0=k1_xboole_0|v1_funct_2(esk9_0,esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_74])).
% 0.21/0.39  cnf(c_0_78, negated_conjecture, (esk6_0=k1_xboole_0|m1_subset_1(esk9_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_74]), c_0_50])).
% 0.21/0.39  cnf(c_0_79, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_52, c_0_55])).
% 0.21/0.39  cnf(c_0_80, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.21/0.39  cnf(c_0_81, negated_conjecture, (r2_hidden(esk1_2(esk8_0,X1),k2_zfmisc_1(esk6_0,esk7_0))|r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.21/0.39  cnf(c_0_82, negated_conjecture, (esk6_0=k1_xboole_0|~r2_relset_1(esk6_0,esk7_0,k1_xboole_0,esk9_0)), inference(spm,[status(thm)],[c_0_64, c_0_70])).
% 0.21/0.39  cnf(c_0_83, negated_conjecture, (esk6_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_77]), c_0_78])).
% 0.21/0.39  cnf(c_0_84, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_55])).
% 0.21/0.39  cnf(c_0_85, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.39  cnf(c_0_86, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk6_0,esk7_0))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_72, c_0_28])).
% 0.21/0.39  cnf(c_0_87, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.21/0.39  cnf(c_0_88, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])])).
% 0.21/0.39  cnf(c_0_89, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_85])).
% 0.21/0.39  cnf(c_0_90, negated_conjecture, (r2_hidden(esk1_2(esk9_0,X1),k2_zfmisc_1(esk6_0,esk7_0))|r1_tarski(esk9_0,X1)), inference(spm,[status(thm)],[c_0_86, c_0_76])).
% 0.21/0.39  cnf(c_0_91, negated_conjecture, (r1_tarski(esk8_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 0.21/0.39  cnf(c_0_92, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_80, c_0_90])).
% 0.21/0.39  cnf(c_0_93, negated_conjecture, (~r2_relset_1(k1_xboole_0,esk7_0,esk8_0,esk9_0)), inference(rw,[status(thm)],[c_0_64, c_0_88])).
% 0.21/0.39  cnf(c_0_94, negated_conjecture, (esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_91])).
% 0.21/0.39  cnf(c_0_95, negated_conjecture, (r1_tarski(esk9_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_88]), c_0_89])).
% 0.21/0.39  cnf(c_0_96, negated_conjecture, (~r2_relset_1(k1_xboole_0,esk7_0,k1_xboole_0,esk9_0)), inference(rw,[status(thm)],[c_0_93, c_0_94])).
% 0.21/0.39  cnf(c_0_97, negated_conjecture, (esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_95])).
% 0.21/0.39  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97]), c_0_84])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 99
% 0.21/0.39  # Proof object clause steps            : 70
% 0.21/0.39  # Proof object formula steps           : 29
% 0.21/0.39  # Proof object conjectures             : 47
% 0.21/0.39  # Proof object clause conjectures      : 44
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 25
% 0.21/0.39  # Proof object initial formulas used   : 14
% 0.21/0.39  # Proof object generating inferences   : 40
% 0.21/0.39  # Proof object simplifying inferences  : 45
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 18
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 40
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 40
% 0.21/0.39  # Processed clauses                    : 282
% 0.21/0.39  # ...of these trivial                  : 1
% 0.21/0.39  # ...subsumed                          : 34
% 0.21/0.39  # ...remaining for further processing  : 247
% 0.21/0.39  # Other redundant clauses eliminated   : 0
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 44
% 0.21/0.39  # Backward-rewritten                   : 95
% 0.21/0.39  # Generated clauses                    : 437
% 0.21/0.39  # ...of the previous two non-trivial   : 416
% 0.21/0.39  # Contextual simplify-reflections      : 3
% 0.21/0.39  # Paramodulations                      : 418
% 0.21/0.39  # Factorizations                       : 1
% 0.21/0.39  # Equation resolutions                 : 18
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 68
% 0.21/0.39  #    Positive orientable unit clauses  : 17
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 0
% 0.21/0.39  #    Non-unit-clauses                  : 51
% 0.21/0.39  # Current number of unprocessed clauses: 199
% 0.21/0.39  # ...number of literals in the above   : 532
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 179
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 2742
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 943
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 79
% 0.21/0.39  # Unit Clause-clause subsumption calls : 185
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 36
% 0.21/0.39  # BW rewrite match successes           : 8
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 8418
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.044 s
% 0.21/0.39  # System time              : 0.006 s
% 0.21/0.39  # Total time               : 0.051 s
% 0.21/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
