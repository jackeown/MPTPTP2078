%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t34_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:44 EDT 2019

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   93 (27310 expanded)
%              Number of clauses        :   80 (9588 expanded)
%              Number of leaves         :    6 (6626 expanded)
%              Depth                    :   23
%              Number of atoms          :  512 (356783 expanded)
%              Number of equality atoms :  204 (148156 expanded)
%              Maximal formula depth    :   31 (   5 average)
%              Maximal clause size      :  130 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t34_funct_2.p',t34_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t34_funct_2.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t34_funct_2.p',redefinition_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t34_funct_2.p',cc1_relset_1)).

fof(t54_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( X2 = k2_funct_1(X1)
            <=> ( k1_relat_1(X2) = k2_relat_1(X1)
                & ! [X3,X4] :
                    ( ( ( r2_hidden(X3,k2_relat_1(X1))
                        & X4 = k1_funct_1(X2,X3) )
                     => ( r2_hidden(X4,k1_relat_1(X1))
                        & X3 = k1_funct_1(X1,X4) ) )
                    & ( ( r2_hidden(X4,k1_relat_1(X1))
                        & X3 = k1_funct_1(X1,X4) )
                     => ( r2_hidden(X3,k2_relat_1(X1))
                        & X4 = k1_funct_1(X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t34_funct_2.p',t54_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t34_funct_2.p',redefinition_k2_relset_1)).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v1_funct_2(X17,X15,X16)
        | X15 = k1_relset_1(X15,X16,X17)
        | X16 = k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X15 != k1_relset_1(X15,X16,X17)
        | v1_funct_2(X17,X15,X16)
        | X16 = k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( ~ v1_funct_2(X17,X15,X16)
        | X15 = k1_relset_1(X15,X16,X17)
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X15 != k1_relset_1(X15,X16,X17)
        | v1_funct_2(X17,X15,X16)
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( ~ v1_funct_2(X17,X15,X16)
        | X17 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X17 != k1_xboole_0
        | v1_funct_2(X17,X15,X16)
        | X15 = k1_xboole_0
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_8,negated_conjecture,(
    ! [X11,X12] :
      ( v1_funct_1(esk3_0)
      & v1_funct_2(esk3_0,esk1_0,esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk2_0,esk1_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
      & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
      & v2_funct_1(esk3_0)
      & ( r2_hidden(X12,esk1_0)
        | ~ r2_hidden(X11,esk2_0)
        | k1_funct_1(esk4_0,X11) != X12 )
      & ( k1_funct_1(esk3_0,X12) = X11
        | ~ r2_hidden(X11,esk2_0)
        | k1_funct_1(esk4_0,X11) != X12 )
      & ( r2_hidden(X11,esk2_0)
        | ~ r2_hidden(X12,esk1_0)
        | k1_funct_1(esk3_0,X12) != X11 )
      & ( k1_funct_1(esk4_0,X11) = X12
        | ~ r2_hidden(X12,esk1_0)
        | k1_funct_1(esk3_0,X12) != X11 )
      & esk1_0 != k1_xboole_0
      & esk2_0 != k1_xboole_0
      & esk4_0 != k2_funct_1(esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k1_relset_1(X27,X28,X29) = k1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_10,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X60,X61,X62] :
      ( ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
      | v1_relat_1(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_15,plain,(
    ! [X42,X43,X44,X45,X46,X47] :
      ( ( k1_relat_1(X43) = k2_relat_1(X42)
        | X43 != k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( r2_hidden(X45,k1_relat_1(X42))
        | ~ r2_hidden(X44,k2_relat_1(X42))
        | X45 != k1_funct_1(X43,X44)
        | X43 != k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( X44 = k1_funct_1(X42,X45)
        | ~ r2_hidden(X44,k2_relat_1(X42))
        | X45 != k1_funct_1(X43,X44)
        | X43 != k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( r2_hidden(X46,k2_relat_1(X42))
        | ~ r2_hidden(X47,k1_relat_1(X42))
        | X46 != k1_funct_1(X42,X47)
        | X43 != k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( X47 = k1_funct_1(X43,X46)
        | ~ r2_hidden(X47,k1_relat_1(X42))
        | X46 != k1_funct_1(X42,X47)
        | X43 != k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( r2_hidden(esk9_2(X42,X43),k1_relat_1(X42))
        | r2_hidden(esk6_2(X42,X43),k2_relat_1(X42))
        | k1_relat_1(X43) != k2_relat_1(X42)
        | X43 = k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( esk8_2(X42,X43) = k1_funct_1(X42,esk9_2(X42,X43))
        | r2_hidden(esk6_2(X42,X43),k2_relat_1(X42))
        | k1_relat_1(X43) != k2_relat_1(X42)
        | X43 = k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( ~ r2_hidden(esk8_2(X42,X43),k2_relat_1(X42))
        | esk9_2(X42,X43) != k1_funct_1(X43,esk8_2(X42,X43))
        | r2_hidden(esk6_2(X42,X43),k2_relat_1(X42))
        | k1_relat_1(X43) != k2_relat_1(X42)
        | X43 = k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( r2_hidden(esk9_2(X42,X43),k1_relat_1(X42))
        | esk7_2(X42,X43) = k1_funct_1(X43,esk6_2(X42,X43))
        | k1_relat_1(X43) != k2_relat_1(X42)
        | X43 = k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( esk8_2(X42,X43) = k1_funct_1(X42,esk9_2(X42,X43))
        | esk7_2(X42,X43) = k1_funct_1(X43,esk6_2(X42,X43))
        | k1_relat_1(X43) != k2_relat_1(X42)
        | X43 = k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( ~ r2_hidden(esk8_2(X42,X43),k2_relat_1(X42))
        | esk9_2(X42,X43) != k1_funct_1(X43,esk8_2(X42,X43))
        | esk7_2(X42,X43) = k1_funct_1(X43,esk6_2(X42,X43))
        | k1_relat_1(X43) != k2_relat_1(X42)
        | X43 = k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( r2_hidden(esk9_2(X42,X43),k1_relat_1(X42))
        | ~ r2_hidden(esk7_2(X42,X43),k1_relat_1(X42))
        | esk6_2(X42,X43) != k1_funct_1(X42,esk7_2(X42,X43))
        | k1_relat_1(X43) != k2_relat_1(X42)
        | X43 = k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( esk8_2(X42,X43) = k1_funct_1(X42,esk9_2(X42,X43))
        | ~ r2_hidden(esk7_2(X42,X43),k1_relat_1(X42))
        | esk6_2(X42,X43) != k1_funct_1(X42,esk7_2(X42,X43))
        | k1_relat_1(X43) != k2_relat_1(X42)
        | X43 = k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( ~ r2_hidden(esk8_2(X42,X43),k2_relat_1(X42))
        | esk9_2(X42,X43) != k1_funct_1(X43,esk8_2(X42,X43))
        | ~ r2_hidden(esk7_2(X42,X43),k1_relat_1(X42))
        | esk6_2(X42,X43) != k1_funct_1(X42,esk7_2(X42,X43))
        | k1_relat_1(X43) != k2_relat_1(X42)
        | X43 = k2_funct_1(X42)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

cnf(c_0_16,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( k1_relset_1(esk2_0,esk1_0,esk4_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_18,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k2_relset_1(X30,X31,X32) = k2_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( r2_hidden(esk9_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk6_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_11]),c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X2,esk1_0)
    | k1_funct_1(esk3_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( k2_funct_1(X1) = esk4_0
    | r2_hidden(esk6_2(X1,esk4_0),k2_relat_1(X1))
    | r2_hidden(esk9_2(X1,esk4_0),k1_relat_1(X1))
    | k2_relat_1(X1) != esk2_0
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_20]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_20]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,plain,
    ( esk8_2(X1,X2) = k1_funct_1(X1,esk9_2(X1,X2))
    | r2_hidden(esk6_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,X1),esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk9_2(esk3_0,esk4_0),esk1_0)
    | r2_hidden(esk6_2(esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(X1,esk9_2(X1,esk4_0)) = esk8_2(X1,esk4_0)
    | k2_funct_1(X1) = esk4_0
    | r2_hidden(esk6_2(X1,esk4_0),k2_relat_1(X1))
    | k2_relat_1(X1) != esk2_0
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = X2
    | ~ r2_hidden(X2,esk1_0)
    | k1_funct_1(esk3_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_43,plain,
    ( r2_hidden(esk6_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk8_2(X1,X2),k2_relat_1(X1))
    | esk9_2(X1,X2) != k1_funct_1(X2,esk8_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk9_2(esk3_0,esk4_0)),esk2_0)
    | r2_hidden(esk6_2(esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk3_0,esk9_2(esk3_0,esk4_0)) = esk8_2(esk3_0,esk4_0)
    | r2_hidden(esk6_2(esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk4_0,k1_funct_1(esk3_0,X1)) = X1
    | ~ r2_hidden(X1,esk1_0) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k2_funct_1(X1) = esk4_0
    | r2_hidden(esk6_2(X1,esk4_0),k2_relat_1(X1))
    | k1_funct_1(esk4_0,esk8_2(X1,esk4_0)) != esk9_2(X1,esk4_0)
    | k2_relat_1(X1) != esk2_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk8_2(X1,esk4_0),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk6_2(esk3_0,esk4_0),esk2_0)
    | r2_hidden(esk8_2(esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = X2
    | ~ r2_hidden(X2,esk2_0)
    | k1_funct_1(esk4_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk4_0,k1_funct_1(esk3_0,esk9_2(esk3_0,esk4_0))) = esk9_2(esk3_0,esk4_0)
    | r2_hidden(esk6_2(esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk6_2(esk3_0,esk4_0),esk2_0)
    | k1_funct_1(esk4_0,esk8_2(esk3_0,esk4_0)) != esk9_2(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_32]),c_0_34]),c_0_35]),c_0_36])]),c_0_37]),c_0_48])).

cnf(c_0_52,plain,
    ( r2_hidden(esk9_2(X1,X2),k1_relat_1(X1))
    | esk7_2(X1,X2) = k1_funct_1(X2,esk6_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | k1_funct_1(esk4_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_54,plain,
    ( r2_hidden(esk9_2(X1,X2),k1_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk7_2(X1,X2),k1_relat_1(X1))
    | esk6_2(X1,X2) != k1_funct_1(X1,esk7_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(esk3_0,k1_funct_1(esk4_0,X1)) = X1
    | ~ r2_hidden(X1,esk2_0) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk6_2(esk3_0,esk4_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_45]),c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk4_0,esk6_2(X1,esk4_0)) = esk7_2(X1,esk4_0)
    | k2_funct_1(X1) = esk4_0
    | r2_hidden(esk9_2(X1,esk4_0),k1_relat_1(X1))
    | k2_relat_1(X1) != esk2_0
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k2_funct_1(X1) = esk4_0
    | r2_hidden(esk9_2(X1,esk4_0),k1_relat_1(X1))
    | k1_funct_1(X1,esk7_2(X1,esk4_0)) != esk6_2(X1,esk4_0)
    | k2_relat_1(X1) != esk2_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk7_2(X1,esk4_0),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(esk3_0,k1_funct_1(esk4_0,esk6_2(esk3_0,esk4_0))) = esk6_2(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk4_0,esk6_2(esk3_0,esk4_0)) = esk7_2(esk3_0,esk4_0)
    | r2_hidden(esk9_2(esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,esk6_2(esk3_0,esk4_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_56])).

cnf(c_0_63,plain,
    ( esk8_2(X1,X2) = k1_funct_1(X1,esk9_2(X1,X2))
    | esk7_2(X1,X2) = k1_funct_1(X2,esk6_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk9_2(esk3_0,esk4_0),esk1_0)
    | k1_funct_1(esk3_0,esk7_2(esk3_0,esk4_0)) != esk6_2(esk3_0,esk4_0)
    | ~ r2_hidden(esk7_2(esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_32]),c_0_33]),c_0_34]),c_0_33]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(esk3_0,esk7_2(esk3_0,esk4_0)) = esk6_2(esk3_0,esk4_0)
    | r2_hidden(esk9_2(esk3_0,esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk9_2(esk3_0,esk4_0),esk1_0)
    | r2_hidden(esk7_2(esk3_0,esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(esk4_0,esk6_2(X1,esk4_0)) = esk7_2(X1,esk4_0)
    | k1_funct_1(X1,esk9_2(X1,esk4_0)) = esk8_2(X1,esk4_0)
    | k2_funct_1(X1) = esk4_0
    | k2_relat_1(X1) != esk2_0
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_68,plain,
    ( esk7_2(X1,X2) = k1_funct_1(X2,esk6_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk8_2(X1,X2),k2_relat_1(X1))
    | esk9_2(X1,X2) != k1_funct_1(X2,esk8_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk9_2(esk3_0,esk4_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(esk3_0,esk9_2(esk3_0,esk4_0)) = esk8_2(esk3_0,esk4_0)
    | k1_funct_1(esk4_0,esk6_2(esk3_0,esk4_0)) = esk7_2(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_32]),c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_71,negated_conjecture,
    ( k1_funct_1(esk4_0,esk6_2(X1,esk4_0)) = esk7_2(X1,esk4_0)
    | k2_funct_1(X1) = esk4_0
    | k1_funct_1(esk4_0,esk8_2(X1,esk4_0)) != esk9_2(X1,esk4_0)
    | k2_relat_1(X1) != esk2_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk8_2(X1,esk4_0),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(esk4_0,k1_funct_1(esk3_0,esk9_2(esk3_0,esk4_0))) = esk9_2(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( k1_funct_1(esk3_0,esk9_2(esk3_0,esk4_0)) = esk8_2(esk3_0,esk4_0)
    | r2_hidden(esk7_2(esk3_0,esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk9_2(esk3_0,esk4_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_69])).

cnf(c_0_75,plain,
    ( esk8_2(X1,X2) = k1_funct_1(X1,esk9_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk7_2(X1,X2),k1_relat_1(X1))
    | esk6_2(X1,X2) != k1_funct_1(X1,esk7_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_76,negated_conjecture,
    ( k1_funct_1(esk4_0,esk6_2(esk3_0,esk4_0)) = esk7_2(esk3_0,esk4_0)
    | k1_funct_1(esk4_0,esk8_2(esk3_0,esk4_0)) != esk9_2(esk3_0,esk4_0)
    | ~ r2_hidden(esk8_2(esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_32]),c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_77,negated_conjecture,
    ( k1_funct_1(esk4_0,esk8_2(esk3_0,esk4_0)) = esk9_2(esk3_0,esk4_0)
    | r2_hidden(esk7_2(esk3_0,esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk7_2(esk3_0,esk4_0),esk1_0)
    | r2_hidden(esk8_2(esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k1_funct_1(X1,esk9_2(X1,esk4_0)) = esk8_2(X1,esk4_0)
    | k2_funct_1(X1) = esk4_0
    | k1_funct_1(X1,esk7_2(X1,esk4_0)) != esk6_2(X1,esk4_0)
    | k2_relat_1(X1) != esk2_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk7_2(X1,esk4_0),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(esk4_0,esk6_2(esk3_0,esk4_0)) = esk7_2(esk3_0,esk4_0)
    | r2_hidden(esk7_2(esk3_0,esk4_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( k1_funct_1(esk3_0,esk9_2(esk3_0,esk4_0)) = esk8_2(esk3_0,esk4_0)
    | k1_funct_1(esk3_0,esk7_2(esk3_0,esk4_0)) != esk6_2(esk3_0,esk4_0)
    | ~ r2_hidden(esk7_2(esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_32]),c_0_34]),c_0_33]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk7_2(esk3_0,esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( k1_funct_1(esk3_0,esk9_2(esk3_0,esk4_0)) = esk8_2(esk3_0,esk4_0)
    | k1_funct_1(esk3_0,esk7_2(esk3_0,esk4_0)) != esk6_2(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_84,plain,
    ( X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk8_2(X1,X2),k2_relat_1(X1))
    | esk9_2(X1,X2) != k1_funct_1(X2,esk8_2(X1,X2))
    | ~ r2_hidden(esk7_2(X1,X2),k1_relat_1(X1))
    | esk6_2(X1,X2) != k1_funct_1(X1,esk7_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(esk3_0,esk9_2(esk3_0,esk4_0)) = esk8_2(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_70]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( k2_funct_1(X1) = esk4_0
    | k1_funct_1(esk4_0,esk8_2(X1,esk4_0)) != esk9_2(X1,esk4_0)
    | k1_funct_1(X1,esk7_2(X1,esk4_0)) != esk6_2(X1,esk4_0)
    | k2_relat_1(X1) != esk2_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk7_2(X1,esk4_0),k1_relat_1(X1))
    | ~ r2_hidden(esk8_2(X1,esk4_0),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk8_2(esk3_0,esk4_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( k1_funct_1(esk4_0,esk8_2(esk3_0,esk4_0)) = esk9_2(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_72,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( k1_funct_1(esk4_0,esk8_2(esk3_0,esk4_0)) != esk9_2(esk3_0,esk4_0)
    | k1_funct_1(esk3_0,esk7_2(esk3_0,esk4_0)) != esk6_2(esk3_0,esk4_0)
    | ~ r2_hidden(esk8_2(esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_32]),c_0_34]),c_0_33]),c_0_35]),c_0_36])]),c_0_37]),c_0_82])])).

cnf(c_0_90,negated_conjecture,
    ( k1_funct_1(esk4_0,esk6_2(esk3_0,esk4_0)) = esk7_2(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_87])]),c_0_88])])).

cnf(c_0_91,negated_conjecture,
    ( k1_funct_1(esk3_0,esk7_2(esk3_0,esk4_0)) != esk6_2(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_87])]),c_0_88])])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_90]),c_0_91]),
    [proof]).
%------------------------------------------------------------------------------
