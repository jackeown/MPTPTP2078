%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t148_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:31 EDT 2019

% Result     : Theorem 5.20s
% Output     : CNFRefutation 5.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  99 expanded)
%              Number of clauses        :   27 (  38 expanded)
%              Number of leaves         :    3 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :  260 (1267 expanded)
%              Number of equality atoms :   66 ( 344 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t145_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( X2 = k1_xboole_0
             => X1 = k1_xboole_0 )
           => ( r1_partfun1(X3,X4)
            <=> ! [X5] :
                  ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t148_funct_2.p',t145_funct_2)).

fof(t136_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
          & ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X1,X2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ? [X5] :
                  ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                  & k1_funct_1(X4,X5) != k1_funct_1(X3,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t148_funct_2.p',t136_funct_2)).

fof(t148_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
          & ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X1,X2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ~ r1_partfun1(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t148_funct_2.p',t148_funct_2)).

fof(c_0_3,plain,(
    ! [X29,X30,X31,X32,X33] :
      ( ( ~ r1_partfun1(X31,X32)
        | ~ r2_hidden(X33,k1_relset_1(X29,X30,X31))
        | k1_funct_1(X31,X33) = k1_funct_1(X32,X33)
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ v1_funct_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( r2_hidden(esk6_4(X29,X30,X31,X32),k1_relset_1(X29,X30,X31))
        | r1_partfun1(X31,X32)
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ v1_funct_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( k1_funct_1(X31,esk6_4(X29,X30,X31,X32)) != k1_funct_1(X32,esk6_4(X29,X30,X31,X32))
        | r1_partfun1(X31,X32)
        | X30 = k1_xboole_0
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ v1_funct_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( ~ r1_partfun1(X31,X32)
        | ~ r2_hidden(X33,k1_relset_1(X29,X30,X31))
        | k1_funct_1(X31,X33) = k1_funct_1(X32,X33)
        | X29 != k1_xboole_0
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ v1_funct_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( r2_hidden(esk6_4(X29,X30,X31,X32),k1_relset_1(X29,X30,X31))
        | r1_partfun1(X31,X32)
        | X29 != k1_xboole_0
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ v1_funct_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( k1_funct_1(X31,esk6_4(X29,X30,X31,X32)) != k1_funct_1(X32,esk6_4(X29,X30,X31,X32))
        | r1_partfun1(X31,X32)
        | X29 != k1_xboole_0
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ v1_funct_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_2])])])])])).

fof(c_0_4,plain,(
    ! [X24,X25,X26,X28] :
      ( ( v1_funct_1(esk5_3(X24,X25,X26))
        | X25 = k1_xboole_0
        | ~ v1_funct_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( v1_funct_2(esk5_3(X24,X25,X26),X24,X25)
        | X25 = k1_xboole_0
        | ~ v1_funct_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( m1_subset_1(esk5_3(X24,X25,X26),k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
        | X25 = k1_xboole_0
        | ~ v1_funct_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( ~ r2_hidden(X28,k1_relset_1(X24,X25,X26))
        | k1_funct_1(esk5_3(X24,X25,X26),X28) = k1_funct_1(X26,X28)
        | X25 = k1_xboole_0
        | ~ v1_funct_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( v1_funct_1(esk5_3(X24,X25,X26))
        | X24 != k1_xboole_0
        | ~ v1_funct_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( v1_funct_2(esk5_3(X24,X25,X26),X24,X25)
        | X24 != k1_xboole_0
        | ~ v1_funct_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( m1_subset_1(esk5_3(X24,X25,X26),k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
        | X24 != k1_xboole_0
        | ~ v1_funct_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( ~ r2_hidden(X28,k1_relset_1(X24,X25,X26))
        | k1_funct_1(esk5_3(X24,X25,X26),X28) = k1_funct_1(X26,X28)
        | X24 != k1_xboole_0
        | ~ v1_funct_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t136_funct_2])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ~ ( ( X2 = k1_xboole_0
             => X1 = k1_xboole_0 )
            & ! [X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X1,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ~ r1_partfun1(X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t148_funct_2])).

cnf(c_0_6,plain,
    ( r1_partfun1(X1,X4)
    | X3 = k1_xboole_0
    | k1_funct_1(X1,esk6_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk6_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( k1_funct_1(esk5_3(X2,X3,X4),X1) = k1_funct_1(X4,X1)
    | X3 = k1_xboole_0
    | ~ r2_hidden(X1,k1_relset_1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( v1_funct_1(esk5_3(X1,X2,X3))
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( r1_partfun1(X1,X4)
    | k1_funct_1(X1,esk6_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk6_4(X2,X3,X1,X4))
    | X2 != k1_xboole_0
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_10,plain,
    ( k1_funct_1(esk5_3(X2,X3,X4),X1) = k1_funct_1(X4,X1)
    | ~ r2_hidden(X1,k1_relset_1(X2,X3,X4))
    | X2 != k1_xboole_0
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( v1_funct_1(esk5_3(X1,X2,X3))
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_12,negated_conjecture,(
    ! [X9] :
      ( v1_funct_1(esk3_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & ( esk2_0 != k1_xboole_0
        | esk1_0 = k1_xboole_0 )
      & ( ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,esk1_0,esk2_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
        | ~ r1_partfun1(esk3_0,X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r1_partfun1(X3,esk5_3(X4,X1,X5))
    | k1_funct_1(X3,esk6_4(X6,X2,X3,esk5_3(X4,X1,X5))) != k1_funct_1(X5,esk6_4(X6,X2,X3,esk5_3(X4,X1,X5)))
    | ~ r2_hidden(esk6_4(X6,X2,X3,esk5_3(X4,X1,X5)),k1_relset_1(X4,X1,X5))
    | ~ v1_funct_2(esk5_3(X4,X1,X5),X6,X2)
    | ~ m1_subset_1(esk5_3(X4,X1,X5),k1_zfmisc_1(k2_zfmisc_1(X6,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X6,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])).

cnf(c_0_14,plain,
    ( r1_partfun1(X1,esk5_3(X2,X3,X4))
    | k1_funct_1(X1,esk6_4(X5,X6,X1,esk5_3(X2,X3,X4))) != k1_funct_1(X4,esk6_4(X5,X6,X1,esk5_3(X2,X3,X4)))
    | X5 != k1_xboole_0
    | X2 != k1_xboole_0
    | ~ r2_hidden(esk6_4(X5,X6,X1,esk5_3(X2,X3,X4)),k1_relset_1(X2,X3,X4))
    | ~ v1_funct_2(esk5_3(X2,X3,X4),X5,X6)
    | ~ m1_subset_1(esk5_3(X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ r1_partfun1(esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v1_funct_2(esk5_3(X1,X2,X3),X1,X2)
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r1_partfun1(X3,esk5_3(X4,X2,X3))
    | ~ r2_hidden(esk6_4(X5,X1,X3,esk5_3(X4,X2,X3)),k1_relset_1(X4,X2,X3))
    | ~ v1_funct_2(esk5_3(X4,X2,X3),X5,X1)
    | ~ m1_subset_1(esk5_3(X4,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X5,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),k1_relset_1(X1,X2,X3))
    | r1_partfun1(X3,X4)
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_20,plain,
    ( v1_funct_2(esk5_3(X1,X2,X3),X1,X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,plain,
    ( r1_partfun1(X1,esk5_3(X2,X3,X1))
    | X4 != k1_xboole_0
    | X2 != k1_xboole_0
    | ~ r2_hidden(esk6_4(X4,X5,X1,esk5_3(X2,X3,X1)),k1_relset_1(X2,X3,X1))
    | ~ v1_funct_2(esk5_3(X2,X3,X1),X4,X5)
    | ~ m1_subset_1(esk5_3(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),k1_relset_1(X1,X2,X3))
    | r1_partfun1(X3,X4)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_24,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_partfun1(esk3_0,esk5_3(esk1_0,esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_8]),c_0_17])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | r1_partfun1(X2,esk5_3(X3,X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_8]),c_0_17]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | ~ r1_partfun1(esk3_0,esk5_3(esk1_0,esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_20]),c_0_11]),c_0_21])).

cnf(c_0_29,plain,
    ( r1_partfun1(X1,esk5_3(X2,X3,X1))
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_11]),c_0_21]),c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_26]),c_0_27])])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
