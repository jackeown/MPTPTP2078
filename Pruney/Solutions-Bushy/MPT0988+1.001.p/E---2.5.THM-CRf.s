%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0988+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:31 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   89 (14977 expanded)
%              Number of clauses        :   76 (5245 expanded)
%              Number of leaves         :    6 (3639 expanded)
%              Depth                    :   19
%              Number of atoms          :  493 (194665 expanded)
%              Number of equality atoms :  203 (81212 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

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
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k2_relset_1(X16,X17,X18) = k2_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_8,negated_conjecture,(
    ! [X33,X34] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk5_0,esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk6_0,esk5_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))
      & k2_relset_1(esk5_0,esk6_0,esk7_0) = esk6_0
      & v2_funct_1(esk7_0)
      & ( r2_hidden(X34,esk5_0)
        | ~ r2_hidden(X33,esk6_0)
        | k1_funct_1(esk8_0,X33) != X34 )
      & ( k1_funct_1(esk7_0,X34) = X33
        | ~ r2_hidden(X33,esk6_0)
        | k1_funct_1(esk8_0,X33) != X34 )
      & ( r2_hidden(X33,esk6_0)
        | ~ r2_hidden(X34,esk5_0)
        | k1_funct_1(esk7_0,X34) != X33 )
      & ( k1_funct_1(esk8_0,X33) = X34
        | ~ r2_hidden(X34,esk5_0)
        | k1_funct_1(esk7_0,X34) != X33 )
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk8_0 != k2_funct_1(esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k1_relset_1(X13,X14,X15) = k1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_11,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( k1_relat_1(X20) = k2_relat_1(X19)
        | X20 != k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(X22,k1_relat_1(X19))
        | ~ r2_hidden(X21,k2_relat_1(X19))
        | X22 != k1_funct_1(X20,X21)
        | X20 != k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( X21 = k1_funct_1(X19,X22)
        | ~ r2_hidden(X21,k2_relat_1(X19))
        | X22 != k1_funct_1(X20,X21)
        | X20 != k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(X23,k2_relat_1(X19))
        | ~ r2_hidden(X24,k1_relat_1(X19))
        | X23 != k1_funct_1(X19,X24)
        | X20 != k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( X24 = k1_funct_1(X20,X23)
        | ~ r2_hidden(X24,k1_relat_1(X19))
        | X23 != k1_funct_1(X19,X24)
        | X20 != k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(esk4_2(X19,X20),k1_relat_1(X19))
        | r2_hidden(esk1_2(X19,X20),k2_relat_1(X19))
        | k1_relat_1(X20) != k2_relat_1(X19)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( esk3_2(X19,X20) = k1_funct_1(X19,esk4_2(X19,X20))
        | r2_hidden(esk1_2(X19,X20),k2_relat_1(X19))
        | k1_relat_1(X20) != k2_relat_1(X19)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(esk3_2(X19,X20),k2_relat_1(X19))
        | esk4_2(X19,X20) != k1_funct_1(X20,esk3_2(X19,X20))
        | r2_hidden(esk1_2(X19,X20),k2_relat_1(X19))
        | k1_relat_1(X20) != k2_relat_1(X19)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(esk4_2(X19,X20),k1_relat_1(X19))
        | esk2_2(X19,X20) = k1_funct_1(X20,esk1_2(X19,X20))
        | k1_relat_1(X20) != k2_relat_1(X19)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( esk3_2(X19,X20) = k1_funct_1(X19,esk4_2(X19,X20))
        | esk2_2(X19,X20) = k1_funct_1(X20,esk1_2(X19,X20))
        | k1_relat_1(X20) != k2_relat_1(X19)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(esk3_2(X19,X20),k2_relat_1(X19))
        | esk4_2(X19,X20) != k1_funct_1(X20,esk3_2(X19,X20))
        | esk2_2(X19,X20) = k1_funct_1(X20,esk1_2(X19,X20))
        | k1_relat_1(X20) != k2_relat_1(X19)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(esk4_2(X19,X20),k1_relat_1(X19))
        | ~ r2_hidden(esk2_2(X19,X20),k1_relat_1(X19))
        | esk1_2(X19,X20) != k1_funct_1(X19,esk2_2(X19,X20))
        | k1_relat_1(X20) != k2_relat_1(X19)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( esk3_2(X19,X20) = k1_funct_1(X19,esk4_2(X19,X20))
        | ~ r2_hidden(esk2_2(X19,X20),k1_relat_1(X19))
        | esk1_2(X19,X20) != k1_funct_1(X19,esk2_2(X19,X20))
        | k1_relat_1(X20) != k2_relat_1(X19)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(esk3_2(X19,X20),k2_relat_1(X19))
        | esk4_2(X19,X20) != k1_funct_1(X20,esk3_2(X19,X20))
        | ~ r2_hidden(esk2_2(X19,X20),k1_relat_1(X19))
        | esk1_2(X19,X20) != k1_funct_1(X19,esk2_2(X19,X20))
        | k1_relat_1(X20) != k2_relat_1(X19)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

cnf(c_0_12,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( k2_relset_1(esk5_0,esk6_0,esk7_0) = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v1_funct_2(X12,X10,X11)
        | X10 = k1_relset_1(X10,X11,X12)
        | X11 = k1_xboole_0
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( X10 != k1_relset_1(X10,X11,X12)
        | v1_funct_2(X12,X10,X11)
        | X11 = k1_xboole_0
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( ~ v1_funct_2(X12,X10,X11)
        | X10 = k1_relset_1(X10,X11,X12)
        | X10 != k1_xboole_0
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( X10 != k1_relset_1(X10,X11,X12)
        | v1_funct_2(X12,X10,X11)
        | X10 != k1_xboole_0
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( ~ v1_funct_2(X12,X10,X11)
        | X12 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 != k1_xboole_0
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( X12 != k1_xboole_0
        | v1_funct_2(X12,X10,X11)
        | X10 = k1_xboole_0
        | X11 != k1_xboole_0
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_17,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( esk3_2(X1,X2) = k1_funct_1(X1,esk4_2(X1,X2))
    | r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( k2_relat_1(esk7_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_24,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k1_relset_1(esk6_0,esk5_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X2,esk6_0)
    | k1_funct_1(esk8_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,X1)) = esk3_2(esk7_0,X1)
    | X1 = k2_funct_1(esk7_0)
    | r2_hidden(esk1_2(esk7_0,X1),esk6_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_18]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( esk8_0 != k2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,plain,
    ( esk3_2(X1,X2) = k1_funct_1(X1,esk4_2(X1,X2))
    | esk2_2(X1,X2) = k1_funct_1(X2,esk1_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,X1),esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0)
    | r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,X1)) = esk3_2(esk7_0,X1)
    | k1_funct_1(X1,esk1_2(esk7_0,X1)) = esk2_2(esk7_0,X1)
    | X1 = k2_funct_1(esk7_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_20]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_41,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_13]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = X2
    | ~ r2_hidden(X2,esk6_0)
    | k1_funct_1(esk8_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_44,plain,
    ( esk3_2(X1,X2) = k1_funct_1(X1,esk4_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | esk1_2(X1,X2) != k1_funct_1(X1,esk2_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0)
    | r2_hidden(k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0)
    | k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk5_0)
    | k1_funct_1(esk7_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_48,negated_conjecture,
    ( X1 = k2_funct_1(esk7_0)
    | r2_hidden(esk4_2(esk7_0,X1),esk5_0)
    | r2_hidden(esk1_2(esk7_0,X1),esk6_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_20]),c_0_21]),c_0_42]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk8_0,X1)) = X1
    | ~ r2_hidden(X1,esk6_0) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,X1)) = esk3_2(esk7_0,X1)
    | X1 = k2_funct_1(esk7_0)
    | k1_funct_1(esk7_0,esk2_2(esk7_0,X1)) != esk1_2(esk7_0,X1)
    | k1_relat_1(X1) != esk6_0
    | ~ r2_hidden(esk2_2(esk7_0,X1),esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_42]),c_0_21]),c_0_20]),c_0_22]),c_0_23])])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0)
    | r2_hidden(esk2_2(esk7_0,esk8_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | esk2_2(X1,X2) = k1_funct_1(X2,esk1_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)
    | r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0))) = esk1_2(esk7_0,esk8_0)
    | k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0)
    | k1_funct_1(esk7_0,esk2_2(esk7_0,esk8_0)) != esk1_2(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(X1,esk1_2(esk7_0,X1)) = esk2_2(esk7_0,X1)
    | X1 = k2_funct_1(esk7_0)
    | r2_hidden(esk4_2(esk7_0,X1),esk5_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_20]),c_0_42]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk8_0,X1) = X2
    | ~ r2_hidden(X2,esk5_0)
    | k1_funct_1(esk7_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X2,esk3_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)),esk6_0)
    | r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) = esk3_2(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_46]),c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0)
    | r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_63,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(esk7_0,X1)) = X1
    | ~ r2_hidden(X1,esk5_0) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( X1 = k2_funct_1(esk7_0)
    | r2_hidden(esk1_2(esk7_0,X1),esk6_0)
    | k1_funct_1(X1,esk3_2(esk7_0,X1)) != esk4_2(esk7_0,X1)
    | k1_relat_1(X1) != esk6_0
    | ~ r2_hidden(esk3_2(esk7_0,X1),esk6_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_21]),c_0_20]),c_0_22]),c_0_23])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)
    | r2_hidden(esk3_2(esk7_0,esk8_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( esk2_2(X1,X2) = k1_funct_1(X2,esk1_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X2,esk3_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0)
    | r2_hidden(k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))) = esk4_2(esk7_0,esk8_0)
    | r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_54])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0)
    | k1_funct_1(esk8_0,esk3_2(esk7_0,esk8_0)) != esk4_2(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(X1,esk1_2(esk7_0,X1)) = esk2_2(esk7_0,X1)
    | X1 = k2_funct_1(esk7_0)
    | k1_funct_1(X1,esk3_2(esk7_0,X1)) != esk4_2(esk7_0,X1)
    | k1_relat_1(X1) != esk6_0
    | ~ r2_hidden(esk3_2(esk7_0,X1),esk6_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_21]),c_0_20]),c_0_22]),c_0_23])])).

cnf(c_0_71,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0)
    | r2_hidden(esk3_2(esk7_0,esk8_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_67,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,esk8_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_61]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))) = esk4_2(esk7_0,esk8_0)
    | k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_62])).

cnf(c_0_74,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0)
    | k1_funct_1(esk8_0,esk3_2(esk7_0,esk8_0)) != esk4_2(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_75,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | esk1_2(X1,X2) != k1_funct_1(X1,esk2_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0)) = esk2_2(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_61]),c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( X1 = k2_funct_1(esk7_0)
    | r2_hidden(esk4_2(esk7_0,X1),esk5_0)
    | k1_funct_1(esk7_0,esk2_2(esk7_0,X1)) != esk1_2(esk7_0,X1)
    | k1_relat_1(X1) != esk6_0
    | ~ r2_hidden(esk2_2(esk7_0,X1),esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_42]),c_0_21]),c_0_20]),c_0_22]),c_0_23])])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk2_2(esk7_0,esk8_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk8_0,esk1_2(esk7_0,esk8_0))) = esk1_2(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0)
    | k1_funct_1(esk7_0,esk2_2(esk7_0,esk8_0)) != esk1_2(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_82,negated_conjecture,
    ( k1_funct_1(esk7_0,esk2_2(esk7_0,esk8_0)) = esk1_2(esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_80,c_0_77])).

cnf(c_0_83,plain,
    ( X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X2,esk3_2(X1,X2))
    | ~ r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | esk1_2(X1,X2) != k1_funct_1(X1,esk2_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_85,negated_conjecture,
    ( X1 = k2_funct_1(esk7_0)
    | k1_funct_1(esk7_0,esk2_2(esk7_0,X1)) != esk1_2(esk7_0,X1)
    | k1_funct_1(X1,esk3_2(esk7_0,X1)) != esk4_2(esk7_0,X1)
    | k1_relat_1(X1) != esk6_0
    | ~ r2_hidden(esk2_2(esk7_0,X1),esk5_0)
    | ~ r2_hidden(esk3_2(esk7_0,X1),esk6_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_42]),c_0_21]),c_0_21]),c_0_20]),c_0_22]),c_0_23])])).

cnf(c_0_86,negated_conjecture,
    ( k1_funct_1(esk8_0,esk3_2(esk7_0,esk8_0)) = esk4_2(esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_84]),c_0_61])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk8_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_84]),c_0_61])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_79]),c_0_30]),c_0_31]),c_0_32])]),c_0_33]),c_0_82]),c_0_86]),c_0_87])]),
    [proof]).

%------------------------------------------------------------------------------
