%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:58 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 (4639 expanded)
%              Number of clauses        :   73 (1758 expanded)
%              Number of leaves         :    8 (1125 expanded)
%              Depth                    :   17
%              Number of atoms          :  407 (50102 expanded)
%              Number of equality atoms :  188 (20849 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( ( k2_relset_1(X1,X2,X3) = X2
              & v2_funct_1(X3)
              & ! [X5,X6] :
                  ( ( ( r2_hidden(X5,X2)
                      & k1_funct_1(X4,X5) = X6 )
                   => ( r2_hidden(X6,X1)
                      & k1_funct_1(X3,X6) = X5 ) )
                  & ( ( r2_hidden(X6,X1)
                      & k1_funct_1(X3,X6) = X5 )
                   => ( r2_hidden(X5,X2)
                      & k1_funct_1(X4,X5) = X6 ) ) ) )
           => ( X1 = k1_xboole_0
              | X2 = k1_xboole_0
              | X4 = k2_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_2)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t60_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k1_relat_1(X1) = k2_relat_1(X2)
              & k2_relat_1(X1) = k1_relat_1(X2)
              & ! [X3,X4] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X4,k1_relat_1(X2)) )
                 => ( k1_funct_1(X1,X3) = X4
                  <=> k1_funct_1(X2,X4) = X3 ) ) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( ( k2_relset_1(X1,X2,X3) = X2
                & v2_funct_1(X3)
                & ! [X5,X6] :
                    ( ( ( r2_hidden(X5,X2)
                        & k1_funct_1(X4,X5) = X6 )
                     => ( r2_hidden(X6,X1)
                        & k1_funct_1(X3,X6) = X5 ) )
                    & ( ( r2_hidden(X6,X1)
                        & k1_funct_1(X3,X6) = X5 )
                     => ( r2_hidden(X5,X2)
                        & k1_funct_1(X4,X5) = X6 ) ) ) )
             => ( X1 = k1_xboole_0
                | X2 = k1_xboole_0
                | X4 = k2_funct_1(X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_funct_2])).

fof(c_0_9,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_relat_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_10,negated_conjecture,(
    ! [X38,X39] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk6_0,esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk7_0,esk6_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk6_0)))
      & k2_relset_1(esk6_0,esk7_0,esk8_0) = esk7_0
      & v2_funct_1(esk8_0)
      & ( r2_hidden(X39,esk6_0)
        | ~ r2_hidden(X38,esk7_0)
        | k1_funct_1(esk9_0,X38) != X39 )
      & ( k1_funct_1(esk8_0,X39) = X38
        | ~ r2_hidden(X38,esk7_0)
        | k1_funct_1(esk9_0,X38) != X39 )
      & ( r2_hidden(X38,esk7_0)
        | ~ r2_hidden(X39,esk6_0)
        | k1_funct_1(esk8_0,X39) != X38 )
      & ( k1_funct_1(esk9_0,X38) = X39
        | ~ r2_hidden(X39,esk6_0)
        | k1_funct_1(esk8_0,X39) != X38 )
      & esk6_0 != k1_xboole_0
      & esk7_0 != k1_xboole_0
      & esk9_0 != k2_funct_1(esk8_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X9,X10] : v1_relat_1(k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_12,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k1_relset_1(X25,X26,X27) = k1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_13,plain,(
    ! [X11,X12,X13,X15,X16,X17,X19] :
      ( ( r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X11))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X13 = k1_funct_1(X11,esk1_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(X16,k1_relat_1(X11))
        | X15 != k1_funct_1(X11,X16)
        | r2_hidden(X15,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk2_2(X11,X17),X17)
        | ~ r2_hidden(X19,k1_relat_1(X11))
        | esk2_2(X11,X17) != k1_funct_1(X11,X19)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk3_2(X11,X17),k1_relat_1(X11))
        | r2_hidden(esk2_2(X11,X17),X17)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk2_2(X11,X17) = k1_funct_1(X11,esk3_2(X11,X17))
        | r2_hidden(esk2_2(X11,X17),X17)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_14,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X31,X32,X33] :
      ( ( ~ v1_funct_2(X33,X31,X32)
        | X31 = k1_relset_1(X31,X32,X33)
        | X32 = k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X31 != k1_relset_1(X31,X32,X33)
        | v1_funct_2(X33,X31,X32)
        | X32 = k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( ~ v1_funct_2(X33,X31,X32)
        | X31 = k1_relset_1(X31,X32,X33)
        | X31 != k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X31 != k1_relset_1(X31,X32,X33)
        | v1_funct_2(X33,X31,X32)
        | X31 != k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( ~ v1_funct_2(X33,X31,X32)
        | X33 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X33 != k1_xboole_0
        | v1_funct_2(X33,X31,X32)
        | X31 = k1_xboole_0
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_18,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( esk2_2(X1,X2) = k1_funct_1(X1,esk3_2(X1,X2))
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_22,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k1_relset_1(esk7_0,esk6_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk6_0)
    | k1_funct_1(esk8_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | esk2_2(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk9_0,esk3_2(esk9_0,X1)) = esk2_2(esk9_0,X1)
    | X1 = k2_relat_1(esk9_0)
    | r2_hidden(esk2_2(esk9_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_15]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,X1),esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk9_0,X1) = X2
    | ~ r2_hidden(X2,esk6_0)
    | k1_funct_1(esk8_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk7_0)
    | k1_funct_1(esk9_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,plain,
    ( r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk9_0,esk3_2(esk9_0,X1)) = esk2_2(esk9_0,X1)
    | X1 = k2_relat_1(esk9_0)
    | esk2_2(esk9_0,X1) != k1_funct_1(esk9_0,X2)
    | ~ r2_hidden(X2,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_20]),c_0_21])])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0)) = esk2_2(esk9_0,esk6_0)
    | k2_relat_1(esk9_0) = esk6_0
    | r2_hidden(k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk8_0,X1)) = X1
    | ~ r2_hidden(X1,esk6_0) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk9_0,X1),esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( X1 = k2_relat_1(esk9_0)
    | r2_hidden(esk3_2(esk9_0,X1),esk7_0)
    | r2_hidden(esk2_2(esk9_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_20]),c_0_29]),c_0_21])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_41,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k2_relset_1(X28,X29,X30) = k2_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0)) = esk2_2(esk9_0,esk6_0)
    | k1_funct_1(esk9_0,esk3_2(esk9_0,X1)) = esk2_2(esk9_0,X1)
    | k2_relat_1(esk9_0) = esk6_0
    | X1 = k2_relat_1(esk9_0)
    | esk2_2(esk9_0,X1) != k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0))) = esk2_2(esk9_0,esk6_0)
    | k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0)) = esk2_2(esk9_0,esk6_0)
    | k2_relat_1(esk9_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_44,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).

cnf(c_0_45,negated_conjecture,
    ( X1 = k2_relat_1(esk9_0)
    | r2_hidden(k1_funct_1(esk9_0,esk3_2(esk9_0,X1)),esk6_0)
    | r2_hidden(esk2_2(esk9_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_48,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( k2_relset_1(esk6_0,esk7_0,esk8_0) = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0)) = esk2_2(esk9_0,esk6_0)
    | k1_funct_1(esk9_0,esk3_2(esk9_0,X1)) = esk2_2(esk9_0,X1)
    | k2_relat_1(esk9_0) = esk6_0
    | X1 = k2_relat_1(esk9_0)
    | esk2_2(esk9_0,X1) != esk2_2(esk9_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(X1) = k2_relat_1(esk9_0)
    | r2_hidden(k1_funct_1(esk9_0,esk3_2(esk9_0,k1_relat_1(X1))),esk6_0)
    | r2_hidden(k1_funct_1(X1,esk2_2(esk9_0,k1_relat_1(X1))),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_40]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k2_relat_1(esk8_0) = esk7_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_40]),c_0_16])])).

fof(c_0_57,plain,(
    ! [X21,X22] :
      ( ( r2_hidden(esk4_2(X21,X22),k1_relat_1(X21))
        | ~ v2_funct_1(X21)
        | k1_relat_1(X21) != k2_relat_1(X22)
        | k2_relat_1(X21) != k1_relat_1(X22)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk5_2(X21,X22),k1_relat_1(X22))
        | ~ v2_funct_1(X21)
        | k1_relat_1(X21) != k2_relat_1(X22)
        | k2_relat_1(X21) != k1_relat_1(X22)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( k1_funct_1(X21,esk4_2(X21,X22)) != esk5_2(X21,X22)
        | k1_funct_1(X22,esk5_2(X21,X22)) != esk4_2(X21,X22)
        | ~ v2_funct_1(X21)
        | k1_relat_1(X21) != k2_relat_1(X22)
        | k2_relat_1(X21) != k1_relat_1(X22)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( k1_funct_1(X21,esk4_2(X21,X22)) = esk5_2(X21,X22)
        | k1_funct_1(X22,esk5_2(X21,X22)) = esk4_2(X21,X22)
        | ~ v2_funct_1(X21)
        | k1_relat_1(X21) != k2_relat_1(X22)
        | k2_relat_1(X21) != k1_relat_1(X22)
        | X22 = k2_funct_1(X21)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_funct_1])])])])])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0)) = esk2_2(esk9_0,esk6_0)
    | k2_relat_1(esk9_0) = esk6_0 ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( k2_relat_1(esk9_0) = esk6_0
    | r2_hidden(k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0)),esk7_0)
    | r2_hidden(k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_56])])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk8_0,k1_funct_1(esk9_0,esk3_2(esk9_0,X1)))) = k1_funct_1(esk9_0,esk3_2(esk9_0,X1))
    | X1 = k2_relat_1(esk9_0)
    | r2_hidden(esk2_2(esk9_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_45])).

cnf(c_0_61,plain,
    ( r2_hidden(esk5_2(X1,X2),k1_relat_1(X2))
    | X2 = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != k2_relat_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( v2_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(esk9_0) = esk6_0
    | r2_hidden(esk2_2(esk9_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( k2_relat_1(esk9_0) = esk6_0
    | r2_hidden(k1_funct_1(esk8_0,k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0))),esk7_0)
    | r2_hidden(k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk8_0,k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0)))) = k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0))
    | k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0))) = esk2_2(esk9_0,esk6_0)
    | k2_relat_1(esk9_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_60])).

cnf(c_0_66,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != k2_relat_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k2_funct_1(esk8_0)
    | r2_hidden(esk5_2(esk8_0,X1),k1_relat_1(X1))
    | k1_relat_1(X1) != esk7_0
    | k2_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_55]),c_0_54]),c_0_53]),c_0_56])])).

cnf(c_0_68,negated_conjecture,
    ( esk9_0 != k2_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_69,negated_conjecture,
    ( k2_relat_1(esk9_0) = esk6_0
    | esk2_2(esk9_0,esk6_0) != k1_funct_1(esk9_0,X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_63]),c_0_29]),c_0_20]),c_0_21])])).

cnf(c_0_70,negated_conjecture,
    ( k2_relat_1(esk9_0) = esk6_0
    | r2_hidden(k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_58])).

cnf(c_0_71,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0))) = esk2_2(esk9_0,esk6_0)
    | k2_relat_1(esk9_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_58])).

cnf(c_0_72,plain,
    ( k1_funct_1(X1,esk4_2(X1,X2)) = esk5_2(X1,X2)
    | k1_funct_1(X2,esk5_2(X1,X2)) = esk4_2(X1,X2)
    | X2 = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != k2_relat_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_73,negated_conjecture,
    ( X1 = k2_funct_1(esk8_0)
    | r2_hidden(esk4_2(esk8_0,X1),esk6_0)
    | k1_relat_1(X1) != esk7_0
    | k2_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_62]),c_0_54]),c_0_55]),c_0_54]),c_0_53]),c_0_56])])).

cnf(c_0_74,negated_conjecture,
    ( k1_funct_1(esk8_0,X1) = X2
    | ~ r2_hidden(X2,esk7_0)
    | k1_funct_1(esk9_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk5_2(esk8_0,esk9_0),esk7_0)
    | k2_relat_1(esk9_0) != esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_29]),c_0_20]),c_0_21])]),c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k2_relat_1(esk9_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_2(esk8_0,X1)) = esk5_2(esk8_0,X1)
    | k1_funct_1(X1,esk5_2(esk8_0,X1)) = esk4_2(esk8_0,X1)
    | X1 = k2_funct_1(esk8_0)
    | k1_relat_1(X1) != esk7_0
    | k2_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_62]),c_0_55]),c_0_54]),c_0_53]),c_0_56])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),esk6_0)
    | k2_relat_1(esk9_0) != esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_29]),c_0_20]),c_0_21])]),c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(esk9_0,X1)) = X1
    | ~ r2_hidden(X1,esk7_0) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk5_2(esk8_0,esk9_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_81,negated_conjecture,
    ( k1_funct_1(esk9_0,esk5_2(esk8_0,esk9_0)) = esk4_2(esk8_0,esk9_0)
    | k1_funct_1(esk8_0,esk4_2(esk8_0,esk9_0)) = esk5_2(esk8_0,esk9_0)
    | k2_relat_1(esk9_0) != esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_29]),c_0_20]),c_0_21])]),c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_76])])).

cnf(c_0_83,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(esk9_0,esk5_2(esk8_0,esk9_0))) = esk5_2(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_2(esk8_0,esk9_0)) = esk5_2(esk8_0,esk9_0)
    | k1_funct_1(esk9_0,esk5_2(esk8_0,esk9_0)) = esk4_2(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_76])])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk4_2(esk8_0,esk9_0))) = esk4_2(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_2(esk8_0,esk9_0)) = esk5_2(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,plain,
    ( X2 = k2_funct_1(X1)
    | k1_funct_1(X1,esk4_2(X1,X2)) != esk5_2(X1,X2)
    | k1_funct_1(X2,esk5_2(X1,X2)) != esk4_2(X1,X2)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != k2_relat_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_88,negated_conjecture,
    ( k1_funct_1(esk9_0,esk5_2(esk8_0,esk9_0)) = esk4_2(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_86]),c_0_29]),c_0_55]),c_0_54]),c_0_76]),c_0_62]),c_0_20]),c_0_53]),c_0_21]),c_0_56])]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:27:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.20/0.54  # and selection function SelectComplexG.
% 0.20/0.54  #
% 0.20/0.54  # Preprocessing time       : 0.015 s
% 0.20/0.54  # Presaturation interreduction done
% 0.20/0.54  
% 0.20/0.54  # Proof found!
% 0.20/0.54  # SZS status Theorem
% 0.20/0.54  # SZS output start CNFRefutation
% 0.20/0.54  fof(t34_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))&![X5, X6]:(((r2_hidden(X5,X2)&k1_funct_1(X4,X5)=X6)=>(r2_hidden(X6,X1)&k1_funct_1(X3,X6)=X5))&((r2_hidden(X6,X1)&k1_funct_1(X3,X6)=X5)=>(r2_hidden(X5,X2)&k1_funct_1(X4,X5)=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_2)).
% 0.20/0.54  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.54  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.54  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.54  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.54  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.54  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.54  fof(t60_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((((v2_funct_1(X1)&k1_relat_1(X1)=k2_relat_1(X2))&k2_relat_1(X1)=k1_relat_1(X2))&![X3, X4]:((r2_hidden(X3,k1_relat_1(X1))&r2_hidden(X4,k1_relat_1(X2)))=>(k1_funct_1(X1,X3)=X4<=>k1_funct_1(X2,X4)=X3)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_1)).
% 0.20/0.54  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))&![X5, X6]:(((r2_hidden(X5,X2)&k1_funct_1(X4,X5)=X6)=>(r2_hidden(X6,X1)&k1_funct_1(X3,X6)=X5))&((r2_hidden(X6,X1)&k1_funct_1(X3,X6)=X5)=>(r2_hidden(X5,X2)&k1_funct_1(X4,X5)=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t34_funct_2])).
% 0.20/0.54  fof(c_0_9, plain, ![X7, X8]:(~v1_relat_1(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_relat_1(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.54  fof(c_0_10, negated_conjecture, ![X38, X39]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk7_0,esk6_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk6_0))))&(((k2_relset_1(esk6_0,esk7_0,esk8_0)=esk7_0&v2_funct_1(esk8_0))&(((r2_hidden(X39,esk6_0)|(~r2_hidden(X38,esk7_0)|k1_funct_1(esk9_0,X38)!=X39))&(k1_funct_1(esk8_0,X39)=X38|(~r2_hidden(X38,esk7_0)|k1_funct_1(esk9_0,X38)!=X39)))&((r2_hidden(X38,esk7_0)|(~r2_hidden(X39,esk6_0)|k1_funct_1(esk8_0,X39)!=X38))&(k1_funct_1(esk9_0,X38)=X39|(~r2_hidden(X39,esk6_0)|k1_funct_1(esk8_0,X39)!=X38)))))&((esk6_0!=k1_xboole_0&esk7_0!=k1_xboole_0)&esk9_0!=k2_funct_1(esk8_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).
% 0.20/0.54  fof(c_0_11, plain, ![X9, X10]:v1_relat_1(k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.54  fof(c_0_12, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k1_relset_1(X25,X26,X27)=k1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.54  fof(c_0_13, plain, ![X11, X12, X13, X15, X16, X17, X19]:((((r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X11))|~r2_hidden(X13,X12)|X12!=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(X13=k1_funct_1(X11,esk1_3(X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(~r2_hidden(X16,k1_relat_1(X11))|X15!=k1_funct_1(X11,X16)|r2_hidden(X15,X12)|X12!=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&((~r2_hidden(esk2_2(X11,X17),X17)|(~r2_hidden(X19,k1_relat_1(X11))|esk2_2(X11,X17)!=k1_funct_1(X11,X19))|X17=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&((r2_hidden(esk3_2(X11,X17),k1_relat_1(X11))|r2_hidden(esk2_2(X11,X17),X17)|X17=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(esk2_2(X11,X17)=k1_funct_1(X11,esk3_2(X11,X17))|r2_hidden(esk2_2(X11,X17),X17)|X17=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.54  cnf(c_0_14, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.54  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_16, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.54  fof(c_0_17, plain, ![X31, X32, X33]:((((~v1_funct_2(X33,X31,X32)|X31=k1_relset_1(X31,X32,X33)|X32=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(X31!=k1_relset_1(X31,X32,X33)|v1_funct_2(X33,X31,X32)|X32=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&((~v1_funct_2(X33,X31,X32)|X31=k1_relset_1(X31,X32,X33)|X31!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(X31!=k1_relset_1(X31,X32,X33)|v1_funct_2(X33,X31,X32)|X31!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&((~v1_funct_2(X33,X31,X32)|X33=k1_xboole_0|X31=k1_xboole_0|X32!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(X33!=k1_xboole_0|v1_funct_2(X33,X31,X32)|X31=k1_xboole_0|X32!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.54  cnf(c_0_18, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.54  cnf(c_0_19, plain, (esk2_2(X1,X2)=k1_funct_1(X1,esk3_2(X1,X2))|r2_hidden(esk2_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.54  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.20/0.54  cnf(c_0_22, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.54  cnf(c_0_23, negated_conjecture, (k1_relset_1(esk7_0,esk6_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 0.20/0.54  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_25, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk6_0)|k1_funct_1(esk8_0,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_27, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(X3,k1_relat_1(X1))|esk2_2(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.54  cnf(c_0_28, negated_conjecture, (k1_funct_1(esk9_0,esk3_2(esk9_0,X1))=esk2_2(esk9_0,X1)|X1=k2_relat_1(esk9_0)|r2_hidden(esk2_2(esk9_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.20/0.54  cnf(c_0_29, negated_conjecture, (k1_relat_1(esk9_0)=esk7_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_15]), c_0_23]), c_0_24])]), c_0_25])).
% 0.20/0.54  cnf(c_0_30, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,X1),esk7_0)|~r2_hidden(X1,esk6_0)), inference(er,[status(thm)],[c_0_26])).
% 0.20/0.54  cnf(c_0_31, negated_conjecture, (k1_funct_1(esk9_0,X1)=X2|~r2_hidden(X2,esk6_0)|k1_funct_1(esk8_0,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X2,esk7_0)|k1_funct_1(esk9_0,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_33, plain, (r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk2_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.54  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk9_0,esk3_2(esk9_0,X1))=esk2_2(esk9_0,X1)|X1=k2_relat_1(esk9_0)|esk2_2(esk9_0,X1)!=k1_funct_1(esk9_0,X2)|~r2_hidden(X2,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_20]), c_0_21])])).
% 0.20/0.54  cnf(c_0_35, negated_conjecture, (k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0))=esk2_2(esk9_0,esk6_0)|k2_relat_1(esk9_0)=esk6_0|r2_hidden(k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0)),esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 0.20/0.54  cnf(c_0_36, negated_conjecture, (k1_funct_1(esk9_0,k1_funct_1(esk8_0,X1))=X1|~r2_hidden(X1,esk6_0)), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.54  cnf(c_0_37, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.54  cnf(c_0_38, negated_conjecture, (r2_hidden(k1_funct_1(esk9_0,X1),esk6_0)|~r2_hidden(X1,esk7_0)), inference(er,[status(thm)],[c_0_32])).
% 0.20/0.54  cnf(c_0_39, negated_conjecture, (X1=k2_relat_1(esk9_0)|r2_hidden(esk3_2(esk9_0,X1),esk7_0)|r2_hidden(esk2_2(esk9_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_20]), c_0_29]), c_0_21])])).
% 0.20/0.54  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  fof(c_0_41, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k2_relset_1(X28,X29,X30)=k2_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.54  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0))=esk2_2(esk9_0,esk6_0)|k1_funct_1(esk9_0,esk3_2(esk9_0,X1))=esk2_2(esk9_0,X1)|k2_relat_1(esk9_0)=esk6_0|X1=k2_relat_1(esk9_0)|esk2_2(esk9_0,X1)!=k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.54  cnf(c_0_43, negated_conjecture, (k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0)))=esk2_2(esk9_0,esk6_0)|k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0))=esk2_2(esk9_0,esk6_0)|k2_relat_1(esk9_0)=esk6_0), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 0.20/0.54  cnf(c_0_44, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).
% 0.20/0.54  cnf(c_0_45, negated_conjecture, (X1=k2_relat_1(esk9_0)|r2_hidden(k1_funct_1(esk9_0,esk3_2(esk9_0,X1)),esk6_0)|r2_hidden(esk2_2(esk9_0,X1),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.54  cnf(c_0_46, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_18, c_0_40])).
% 0.20/0.54  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_48, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_49, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.54  cnf(c_0_50, negated_conjecture, (k2_relset_1(esk6_0,esk7_0,esk8_0)=esk7_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_51, negated_conjecture, (k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0))=esk2_2(esk9_0,esk6_0)|k1_funct_1(esk9_0,esk3_2(esk9_0,X1))=esk2_2(esk9_0,X1)|k2_relat_1(esk9_0)=esk6_0|X1=k2_relat_1(esk9_0)|esk2_2(esk9_0,X1)!=esk2_2(esk9_0,esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.54  cnf(c_0_52, negated_conjecture, (k1_relat_1(X1)=k2_relat_1(esk9_0)|r2_hidden(k1_funct_1(esk9_0,esk3_2(esk9_0,k1_relat_1(X1))),esk6_0)|r2_hidden(k1_funct_1(X1,esk2_2(esk9_0,k1_relat_1(X1))),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.54  cnf(c_0_53, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_54, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_40]), c_0_46]), c_0_47])]), c_0_48])).
% 0.20/0.54  cnf(c_0_55, negated_conjecture, (k2_relat_1(esk8_0)=esk7_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_50])).
% 0.20/0.54  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_40]), c_0_16])])).
% 0.20/0.54  fof(c_0_57, plain, ![X21, X22]:(((r2_hidden(esk4_2(X21,X22),k1_relat_1(X21))|(~v2_funct_1(X21)|k1_relat_1(X21)!=k2_relat_1(X22)|k2_relat_1(X21)!=k1_relat_1(X22))|X22=k2_funct_1(X21)|(~v1_relat_1(X22)|~v1_funct_1(X22))|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(r2_hidden(esk5_2(X21,X22),k1_relat_1(X22))|(~v2_funct_1(X21)|k1_relat_1(X21)!=k2_relat_1(X22)|k2_relat_1(X21)!=k1_relat_1(X22))|X22=k2_funct_1(X21)|(~v1_relat_1(X22)|~v1_funct_1(X22))|(~v1_relat_1(X21)|~v1_funct_1(X21))))&((k1_funct_1(X21,esk4_2(X21,X22))!=esk5_2(X21,X22)|k1_funct_1(X22,esk5_2(X21,X22))!=esk4_2(X21,X22)|(~v2_funct_1(X21)|k1_relat_1(X21)!=k2_relat_1(X22)|k2_relat_1(X21)!=k1_relat_1(X22))|X22=k2_funct_1(X21)|(~v1_relat_1(X22)|~v1_funct_1(X22))|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(k1_funct_1(X21,esk4_2(X21,X22))=esk5_2(X21,X22)|k1_funct_1(X22,esk5_2(X21,X22))=esk4_2(X21,X22)|(~v2_funct_1(X21)|k1_relat_1(X21)!=k2_relat_1(X22)|k2_relat_1(X21)!=k1_relat_1(X22))|X22=k2_funct_1(X21)|(~v1_relat_1(X22)|~v1_funct_1(X22))|(~v1_relat_1(X21)|~v1_funct_1(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_funct_1])])])])])).
% 0.20/0.54  cnf(c_0_58, negated_conjecture, (k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0))=esk2_2(esk9_0,esk6_0)|k2_relat_1(esk9_0)=esk6_0), inference(er,[status(thm)],[c_0_51])).
% 0.20/0.54  cnf(c_0_59, negated_conjecture, (k2_relat_1(esk9_0)=esk6_0|r2_hidden(k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0)),esk7_0)|r2_hidden(k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_56])])).
% 0.20/0.54  cnf(c_0_60, negated_conjecture, (k1_funct_1(esk9_0,k1_funct_1(esk8_0,k1_funct_1(esk9_0,esk3_2(esk9_0,X1))))=k1_funct_1(esk9_0,esk3_2(esk9_0,X1))|X1=k2_relat_1(esk9_0)|r2_hidden(esk2_2(esk9_0,X1),X1)), inference(spm,[status(thm)],[c_0_36, c_0_45])).
% 0.20/0.54  cnf(c_0_61, plain, (r2_hidden(esk5_2(X1,X2),k1_relat_1(X2))|X2=k2_funct_1(X1)|~v2_funct_1(X1)|k1_relat_1(X1)!=k2_relat_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.54  cnf(c_0_62, negated_conjecture, (v2_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_63, negated_conjecture, (k2_relat_1(esk9_0)=esk6_0|r2_hidden(esk2_2(esk9_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_58])).
% 0.20/0.54  cnf(c_0_64, negated_conjecture, (k2_relat_1(esk9_0)=esk6_0|r2_hidden(k1_funct_1(esk8_0,k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0))),esk7_0)|r2_hidden(k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0)),esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_59])).
% 0.20/0.54  cnf(c_0_65, negated_conjecture, (k1_funct_1(esk9_0,k1_funct_1(esk8_0,k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0))))=k1_funct_1(esk9_0,esk3_2(esk9_0,esk6_0))|k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0)))=esk2_2(esk9_0,esk6_0)|k2_relat_1(esk9_0)=esk6_0), inference(spm,[status(thm)],[c_0_36, c_0_60])).
% 0.20/0.54  cnf(c_0_66, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|X2=k2_funct_1(X1)|~v2_funct_1(X1)|k1_relat_1(X1)!=k2_relat_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.54  cnf(c_0_67, negated_conjecture, (X1=k2_funct_1(esk8_0)|r2_hidden(esk5_2(esk8_0,X1),k1_relat_1(X1))|k1_relat_1(X1)!=esk7_0|k2_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_55]), c_0_54]), c_0_53]), c_0_56])])).
% 0.20/0.54  cnf(c_0_68, negated_conjecture, (esk9_0!=k2_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_69, negated_conjecture, (k2_relat_1(esk9_0)=esk6_0|esk2_2(esk9_0,esk6_0)!=k1_funct_1(esk9_0,X1)|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_63]), c_0_29]), c_0_20]), c_0_21])])).
% 0.20/0.54  cnf(c_0_70, negated_conjecture, (k2_relat_1(esk9_0)=esk6_0|r2_hidden(k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0)),esk7_0)), inference(spm,[status(thm)],[c_0_64, c_0_58])).
% 0.20/0.54  cnf(c_0_71, negated_conjecture, (k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk2_2(esk9_0,esk6_0)))=esk2_2(esk9_0,esk6_0)|k2_relat_1(esk9_0)=esk6_0), inference(spm,[status(thm)],[c_0_65, c_0_58])).
% 0.20/0.54  cnf(c_0_72, plain, (k1_funct_1(X1,esk4_2(X1,X2))=esk5_2(X1,X2)|k1_funct_1(X2,esk5_2(X1,X2))=esk4_2(X1,X2)|X2=k2_funct_1(X1)|~v2_funct_1(X1)|k1_relat_1(X1)!=k2_relat_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.54  cnf(c_0_73, negated_conjecture, (X1=k2_funct_1(esk8_0)|r2_hidden(esk4_2(esk8_0,X1),esk6_0)|k1_relat_1(X1)!=esk7_0|k2_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_62]), c_0_54]), c_0_55]), c_0_54]), c_0_53]), c_0_56])])).
% 0.20/0.54  cnf(c_0_74, negated_conjecture, (k1_funct_1(esk8_0,X1)=X2|~r2_hidden(X2,esk7_0)|k1_funct_1(esk9_0,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_75, negated_conjecture, (r2_hidden(esk5_2(esk8_0,esk9_0),esk7_0)|k2_relat_1(esk9_0)!=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_29]), c_0_20]), c_0_21])]), c_0_68])).
% 0.20/0.54  cnf(c_0_76, negated_conjecture, (k2_relat_1(esk9_0)=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.20/0.54  cnf(c_0_77, negated_conjecture, (k1_funct_1(esk8_0,esk4_2(esk8_0,X1))=esk5_2(esk8_0,X1)|k1_funct_1(X1,esk5_2(esk8_0,X1))=esk4_2(esk8_0,X1)|X1=k2_funct_1(esk8_0)|k1_relat_1(X1)!=esk7_0|k2_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_62]), c_0_55]), c_0_54]), c_0_53]), c_0_56])])).
% 0.20/0.54  cnf(c_0_78, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),esk6_0)|k2_relat_1(esk9_0)!=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_29]), c_0_20]), c_0_21])]), c_0_68])).
% 0.20/0.54  cnf(c_0_79, negated_conjecture, (k1_funct_1(esk8_0,k1_funct_1(esk9_0,X1))=X1|~r2_hidden(X1,esk7_0)), inference(er,[status(thm)],[c_0_74])).
% 0.20/0.54  cnf(c_0_80, negated_conjecture, (r2_hidden(esk5_2(esk8_0,esk9_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])])).
% 0.20/0.54  cnf(c_0_81, negated_conjecture, (k1_funct_1(esk9_0,esk5_2(esk8_0,esk9_0))=esk4_2(esk8_0,esk9_0)|k1_funct_1(esk8_0,esk4_2(esk8_0,esk9_0))=esk5_2(esk8_0,esk9_0)|k2_relat_1(esk9_0)!=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_29]), c_0_20]), c_0_21])]), c_0_68])).
% 0.20/0.54  cnf(c_0_82, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_76])])).
% 0.20/0.54  cnf(c_0_83, negated_conjecture, (k1_funct_1(esk8_0,k1_funct_1(esk9_0,esk5_2(esk8_0,esk9_0)))=esk5_2(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.20/0.54  cnf(c_0_84, negated_conjecture, (k1_funct_1(esk8_0,esk4_2(esk8_0,esk9_0))=esk5_2(esk8_0,esk9_0)|k1_funct_1(esk9_0,esk5_2(esk8_0,esk9_0))=esk4_2(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_76])])).
% 0.20/0.54  cnf(c_0_85, negated_conjecture, (k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk4_2(esk8_0,esk9_0)))=esk4_2(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_36, c_0_82])).
% 0.20/0.54  cnf(c_0_86, negated_conjecture, (k1_funct_1(esk8_0,esk4_2(esk8_0,esk9_0))=esk5_2(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.54  cnf(c_0_87, plain, (X2=k2_funct_1(X1)|k1_funct_1(X1,esk4_2(X1,X2))!=esk5_2(X1,X2)|k1_funct_1(X2,esk5_2(X1,X2))!=esk4_2(X1,X2)|~v2_funct_1(X1)|k1_relat_1(X1)!=k2_relat_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.54  cnf(c_0_88, negated_conjecture, (k1_funct_1(esk9_0,esk5_2(esk8_0,esk9_0))=esk4_2(esk8_0,esk9_0)), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.20/0.54  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_86]), c_0_29]), c_0_55]), c_0_54]), c_0_76]), c_0_62]), c_0_20]), c_0_53]), c_0_21]), c_0_56])]), c_0_68]), ['proof']).
% 0.20/0.54  # SZS output end CNFRefutation
% 0.20/0.54  # Proof object total steps             : 90
% 0.20/0.54  # Proof object clause steps            : 73
% 0.20/0.54  # Proof object formula steps           : 17
% 0.20/0.54  # Proof object conjectures             : 62
% 0.20/0.54  # Proof object clause conjectures      : 59
% 0.20/0.54  # Proof object formula conjectures     : 3
% 0.20/0.54  # Proof object initial clauses used    : 28
% 0.20/0.54  # Proof object initial formulas used   : 8
% 0.20/0.54  # Proof object generating inferences   : 36
% 0.20/0.54  # Proof object simplifying inferences  : 86
% 0.20/0.54  # Training examples: 0 positive, 0 negative
% 0.20/0.54  # Parsed axioms                        : 8
% 0.20/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.54  # Initial clauses                      : 35
% 0.20/0.54  # Removed in clause preprocessing      : 0
% 0.20/0.54  # Initial clauses in saturation        : 35
% 0.20/0.54  # Processed clauses                    : 1356
% 0.20/0.54  # ...of these trivial                  : 4
% 0.20/0.54  # ...subsumed                          : 395
% 0.20/0.54  # ...remaining for further processing  : 957
% 0.20/0.54  # Other redundant clauses eliminated   : 13
% 0.20/0.54  # Clauses deleted for lack of memory   : 0
% 0.20/0.54  # Backward-subsumed                    : 99
% 0.20/0.54  # Backward-rewritten                   : 424
% 0.20/0.54  # Generated clauses                    : 11578
% 0.20/0.54  # ...of the previous two non-trivial   : 11891
% 0.20/0.54  # Contextual simplify-reflections      : 2
% 0.20/0.54  # Paramodulations                      : 11565
% 0.20/0.54  # Factorizations                       : 0
% 0.20/0.54  # Equation resolutions                 : 15
% 0.20/0.54  # Propositional unsat checks           : 0
% 0.20/0.54  #    Propositional check models        : 0
% 0.20/0.54  #    Propositional check unsatisfiable : 0
% 0.20/0.54  #    Propositional clauses             : 0
% 0.20/0.54  #    Propositional clauses after purity: 0
% 0.20/0.54  #    Propositional unsat core size     : 0
% 0.20/0.54  #    Propositional preprocessing time  : 0.000
% 0.20/0.54  #    Propositional encoding time       : 0.000
% 0.20/0.54  #    Propositional solver time         : 0.000
% 0.20/0.54  #    Success case prop preproc time    : 0.000
% 0.20/0.54  #    Success case prop encoding time   : 0.000
% 0.20/0.54  #    Success case prop solver time     : 0.000
% 0.20/0.54  # Current number of processed clauses  : 388
% 0.20/0.54  #    Positive orientable unit clauses  : 26
% 0.20/0.54  #    Positive unorientable unit clauses: 0
% 0.20/0.54  #    Negative unit clauses             : 3
% 0.20/0.54  #    Non-unit-clauses                  : 359
% 0.20/0.54  # Current number of unprocessed clauses: 10597
% 0.20/0.54  # ...number of literals in the above   : 49534
% 0.20/0.54  # Current number of archived formulas  : 0
% 0.20/0.54  # Current number of archived clauses   : 558
% 0.20/0.54  # Clause-clause subsumption calls (NU) : 31310
% 0.20/0.54  # Rec. Clause-clause subsumption calls : 2310
% 0.20/0.54  # Non-unit clause-clause subsumptions  : 496
% 0.20/0.54  # Unit Clause-clause subsumption calls : 946
% 0.20/0.54  # Rewrite failures with RHS unbound    : 0
% 0.20/0.54  # BW rewrite match attempts            : 126
% 0.20/0.54  # BW rewrite match successes           : 7
% 0.20/0.54  # Condensation attempts                : 0
% 0.20/0.54  # Condensation successes               : 0
% 0.20/0.54  # Termbank termtop insertions          : 340199
% 0.20/0.55  
% 0.20/0.55  # -------------------------------------------------
% 0.20/0.55  # User time                : 0.200 s
% 0.20/0.55  # System time              : 0.006 s
% 0.20/0.55  # Total time               : 0.207 s
% 0.20/0.55  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
