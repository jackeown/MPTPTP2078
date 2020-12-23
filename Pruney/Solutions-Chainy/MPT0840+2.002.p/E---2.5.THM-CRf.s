%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:42 EST 2020

% Result     : Theorem 18.62s
% Output     : CNFRefutation 18.62s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 310 expanded)
%              Number of clauses        :   39 ( 119 expanded)
%              Number of leaves         :   11 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :  252 (1782 expanded)
%              Number of equality atoms :   33 (  72 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
                     => ! [X6,X7] :
                          ( r2_hidden(k4_tarski(X6,X7),k4_relset_1(X1,X2,X2,X3,X4,X5))
                        <=> ? [X8] :
                              ( m1_subset_1(X8,X2)
                              & r2_hidden(k4_tarski(X6,X8),X4)
                              & r2_hidden(k4_tarski(X8,X7),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ~ v1_xboole_0(X3)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
                       => ! [X6,X7] :
                            ( r2_hidden(k4_tarski(X6,X7),k4_relset_1(X1,X2,X2,X3,X4,X5))
                          <=> ? [X8] :
                                ( m1_subset_1(X8,X2)
                                & r2_hidden(k4_tarski(X6,X8),X4)
                                & r2_hidden(k4_tarski(X8,X7),X5) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_relset_1])).

fof(c_0_12,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | v1_relat_1(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_13,negated_conjecture,(
    ! [X63] :
      ( ~ v1_xboole_0(esk8_0)
      & ~ v1_xboole_0(esk9_0)
      & ~ v1_xboole_0(esk10_0)
      & m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))
      & m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))
      & ( ~ r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))
        | ~ m1_subset_1(X63,esk9_0)
        | ~ r2_hidden(k4_tarski(esk13_0,X63),esk11_0)
        | ~ r2_hidden(k4_tarski(X63,esk14_0),esk12_0) )
      & ( m1_subset_1(esk15_0,esk9_0)
        | r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0)) )
      & ( r2_hidden(k4_tarski(esk13_0,esk15_0),esk11_0)
        | r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0)) )
      & ( r2_hidden(k4_tarski(esk15_0,esk14_0),esk12_0)
        | r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).

fof(c_0_14,plain,(
    ! [X42,X43] : v1_relat_1(k2_zfmisc_1(X42,X43)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_15,plain,(
    ! [X27,X28,X29,X30,X31,X33,X34,X35,X38] :
      ( ( r2_hidden(k4_tarski(X30,esk4_5(X27,X28,X29,X30,X31)),X27)
        | ~ r2_hidden(k4_tarski(X30,X31),X29)
        | X29 != k5_relat_1(X27,X28)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk4_5(X27,X28,X29,X30,X31),X31),X28)
        | ~ r2_hidden(k4_tarski(X30,X31),X29)
        | X29 != k5_relat_1(X27,X28)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X33,X35),X27)
        | ~ r2_hidden(k4_tarski(X35,X34),X28)
        | r2_hidden(k4_tarski(X33,X34),X29)
        | X29 != k5_relat_1(X27,X28)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(esk5_3(X27,X28,X29),esk6_3(X27,X28,X29)),X29)
        | ~ r2_hidden(k4_tarski(esk5_3(X27,X28,X29),X38),X27)
        | ~ r2_hidden(k4_tarski(X38,esk6_3(X27,X28,X29)),X28)
        | X29 = k5_relat_1(X27,X28)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk5_3(X27,X28,X29),esk7_3(X27,X28,X29)),X27)
        | r2_hidden(k4_tarski(esk5_3(X27,X28,X29),esk6_3(X27,X28,X29)),X29)
        | X29 = k5_relat_1(X27,X28)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk7_3(X27,X28,X29),esk6_3(X27,X28,X29)),X28)
        | r2_hidden(k4_tarski(esk5_3(X27,X28,X29),esk6_3(X27,X28,X29)),X29)
        | X29 = k5_relat_1(X27,X28)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_16,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk15_0,esk14_0),esk12_0)
    | r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))
    | r2_hidden(k4_tarski(X1,esk14_0),X2)
    | X2 != k5_relat_1(X3,esk12_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,esk15_0),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk13_0,esk15_0),esk11_0)
    | r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_22]),c_0_18])])).

fof(c_0_26,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X40)
      | ~ v1_relat_1(X41)
      | v1_relat_1(k5_relat_1(X40,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))
    | r2_hidden(k4_tarski(esk13_0,esk14_0),X1)
    | X1 != k5_relat_1(esk11_0,esk12_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_28,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_29,plain,(
    ! [X50,X51,X52,X53,X54,X55] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | k4_relset_1(X50,X51,X52,X53,X54,X55) = k5_relat_1(X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))
    | r2_hidden(k4_tarski(esk13_0,esk14_0),k5_relat_1(X1,X2))
    | k5_relat_1(X1,X2) != k5_relat_1(esk11_0,esk12_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))
    | ~ m1_subset_1(X1,esk9_0)
    | ~ r2_hidden(k4_tarski(esk13_0,X1),esk11_0)
    | ~ r2_hidden(k4_tarski(X1,esk14_0),esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | m1_subset_1(k2_relset_1(X44,X45,X46),k1_zfmisc_1(X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_34,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k2_relset_1(X47,X48,X49) = k2_relat_1(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))
    | r2_hidden(k4_tarski(esk13_0,esk14_0),k5_relat_1(esk11_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_21]),c_0_25])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk13_0,esk14_0),k5_relat_1(esk11_0,esk12_0))
    | ~ r2_hidden(k4_tarski(X1,esk14_0),esk12_0)
    | ~ r2_hidden(k4_tarski(esk13_0,X1),esk11_0)
    | ~ m1_subset_1(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_17]),c_0_22])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk14_0),esk12_0)
    | ~ r2_hidden(k4_tarski(esk13_0,X1),esk11_0)
    | ~ m1_subset_1(X1,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_35]),c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_41,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | m1_subset_1(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_42,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | ~ r2_hidden(X11,X10)
      | r2_hidden(X11,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_44,plain,(
    ! [X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(k4_tarski(esk1_3(X16,X17,X18),X18),X16)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X21,X20),X16)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(esk2_2(X22,X23),X23)
        | ~ r2_hidden(k4_tarski(X25,esk2_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) )
      & ( r2_hidden(esk2_2(X22,X23),X23)
        | r2_hidden(k4_tarski(esk3_2(X22,X23),esk2_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_45,negated_conjecture,
    ( X1 != k5_relat_1(X2,esk12_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk13_0,esk4_5(X2,esk12_0,X1,X3,esk14_0)),esk11_0)
    | ~ r2_hidden(k4_tarski(X3,esk14_0),X1)
    | ~ m1_subset_1(esk4_5(X2,esk12_0,X1,X3,esk14_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_21])])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk11_0),k1_zfmisc_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_49,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(k4_tarski(X1,esk4_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( X1 != k5_relat_1(X2,esk12_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk13_0,esk4_5(X2,esk12_0,X1,X3,esk14_0)),esk11_0)
    | ~ r2_hidden(esk4_5(X2,esk12_0,X1,X3,esk14_0),esk9_0)
    | ~ r2_hidden(k4_tarski(X3,esk14_0),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,k2_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( r2_hidden(esk4_5(X1,X2,X3,X4,X5),X6)
    | X3 != k5_relat_1(X1,X2)
    | X6 != k2_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X4,X5),X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk15_0,esk9_0)
    | r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( X1 != k5_relat_1(esk11_0,esk12_0)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk4_5(esk11_0,esk12_0,X1,esk13_0,esk14_0),esk9_0)
    | ~ r2_hidden(k4_tarski(esk13_0,esk14_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_50]),c_0_25]),c_0_21])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk4_5(X1,X2,X3,X4,X5),esk9_0)
    | k2_relat_1(esk11_0) != k2_relat_1(X1)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X4,X5),X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_54]),c_0_24])).

cnf(c_0_58,negated_conjecture,
    ( X1 != k5_relat_1(esk11_0,esk12_0)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk13_0,esk14_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_21]),c_0_25])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k4_tarski(esk13_0,esk14_0),k5_relat_1(esk11_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_32]),c_0_17]),c_0_22])])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(esk11_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_28]),c_0_21]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:12:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 18.62/18.84  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 18.62/18.84  # and selection function SelectMaxLComplexAvoidPosPred.
% 18.62/18.84  #
% 18.62/18.84  # Preprocessing time       : 0.028 s
% 18.62/18.84  # Presaturation interreduction done
% 18.62/18.84  
% 18.62/18.84  # Proof found!
% 18.62/18.84  # SZS status Theorem
% 18.62/18.84  # SZS output start CNFRefutation
% 18.62/18.84  fof(t51_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>![X6, X7]:(r2_hidden(k4_tarski(X6,X7),k4_relset_1(X1,X2,X2,X3,X4,X5))<=>?[X8]:((m1_subset_1(X8,X2)&r2_hidden(k4_tarski(X6,X8),X4))&r2_hidden(k4_tarski(X8,X7),X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_relset_1)).
% 18.62/18.84  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 18.62/18.84  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 18.62/18.84  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 18.62/18.84  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 18.62/18.84  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 18.62/18.84  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 18.62/18.84  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 18.62/18.84  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 18.62/18.84  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 18.62/18.84  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 18.62/18.84  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>![X6, X7]:(r2_hidden(k4_tarski(X6,X7),k4_relset_1(X1,X2,X2,X3,X4,X5))<=>?[X8]:((m1_subset_1(X8,X2)&r2_hidden(k4_tarski(X6,X8),X4))&r2_hidden(k4_tarski(X8,X7),X5))))))))), inference(assume_negation,[status(cth)],[t51_relset_1])).
% 18.62/18.84  fof(c_0_12, plain, ![X14, X15]:(~v1_relat_1(X14)|(~m1_subset_1(X15,k1_zfmisc_1(X14))|v1_relat_1(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 18.62/18.84  fof(c_0_13, negated_conjecture, ![X63]:(~v1_xboole_0(esk8_0)&(~v1_xboole_0(esk9_0)&(~v1_xboole_0(esk10_0)&(m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))&(m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))&((~r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))|(~m1_subset_1(X63,esk9_0)|~r2_hidden(k4_tarski(esk13_0,X63),esk11_0)|~r2_hidden(k4_tarski(X63,esk14_0),esk12_0)))&(((m1_subset_1(esk15_0,esk9_0)|r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0)))&(r2_hidden(k4_tarski(esk13_0,esk15_0),esk11_0)|r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))))&(r2_hidden(k4_tarski(esk15_0,esk14_0),esk12_0)|r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).
% 18.62/18.84  fof(c_0_14, plain, ![X42, X43]:v1_relat_1(k2_zfmisc_1(X42,X43)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 18.62/18.84  fof(c_0_15, plain, ![X27, X28, X29, X30, X31, X33, X34, X35, X38]:((((r2_hidden(k4_tarski(X30,esk4_5(X27,X28,X29,X30,X31)),X27)|~r2_hidden(k4_tarski(X30,X31),X29)|X29!=k5_relat_1(X27,X28)|~v1_relat_1(X29)|~v1_relat_1(X28)|~v1_relat_1(X27))&(r2_hidden(k4_tarski(esk4_5(X27,X28,X29,X30,X31),X31),X28)|~r2_hidden(k4_tarski(X30,X31),X29)|X29!=k5_relat_1(X27,X28)|~v1_relat_1(X29)|~v1_relat_1(X28)|~v1_relat_1(X27)))&(~r2_hidden(k4_tarski(X33,X35),X27)|~r2_hidden(k4_tarski(X35,X34),X28)|r2_hidden(k4_tarski(X33,X34),X29)|X29!=k5_relat_1(X27,X28)|~v1_relat_1(X29)|~v1_relat_1(X28)|~v1_relat_1(X27)))&((~r2_hidden(k4_tarski(esk5_3(X27,X28,X29),esk6_3(X27,X28,X29)),X29)|(~r2_hidden(k4_tarski(esk5_3(X27,X28,X29),X38),X27)|~r2_hidden(k4_tarski(X38,esk6_3(X27,X28,X29)),X28))|X29=k5_relat_1(X27,X28)|~v1_relat_1(X29)|~v1_relat_1(X28)|~v1_relat_1(X27))&((r2_hidden(k4_tarski(esk5_3(X27,X28,X29),esk7_3(X27,X28,X29)),X27)|r2_hidden(k4_tarski(esk5_3(X27,X28,X29),esk6_3(X27,X28,X29)),X29)|X29=k5_relat_1(X27,X28)|~v1_relat_1(X29)|~v1_relat_1(X28)|~v1_relat_1(X27))&(r2_hidden(k4_tarski(esk7_3(X27,X28,X29),esk6_3(X27,X28,X29)),X28)|r2_hidden(k4_tarski(esk5_3(X27,X28,X29),esk6_3(X27,X28,X29)),X29)|X29=k5_relat_1(X27,X28)|~v1_relat_1(X29)|~v1_relat_1(X28)|~v1_relat_1(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 18.62/18.84  cnf(c_0_16, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 18.62/18.84  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.62/18.84  cnf(c_0_18, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 18.62/18.84  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,X4),X6)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X2,X4),X5)|X6!=k5_relat_1(X3,X5)|~v1_relat_1(X6)|~v1_relat_1(X5)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 18.62/18.84  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk15_0,esk14_0),esk12_0)|r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.62/18.84  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 18.62/18.84  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.62/18.84  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))|r2_hidden(k4_tarski(X1,esk14_0),X2)|X2!=k5_relat_1(X3,esk12_0)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,esk15_0),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 18.62/18.84  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk13_0,esk15_0),esk11_0)|r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.62/18.84  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_22]), c_0_18])])).
% 18.62/18.84  fof(c_0_26, plain, ![X40, X41]:(~v1_relat_1(X40)|~v1_relat_1(X41)|v1_relat_1(k5_relat_1(X40,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 18.62/18.84  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))|r2_hidden(k4_tarski(esk13_0,esk14_0),X1)|X1!=k5_relat_1(esk11_0,esk12_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 18.62/18.84  cnf(c_0_28, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 18.62/18.84  fof(c_0_29, plain, ![X50, X51, X52, X53, X54, X55]:(~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|k4_relset_1(X50,X51,X52,X53,X54,X55)=k5_relat_1(X54,X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 18.62/18.84  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))|r2_hidden(k4_tarski(esk13_0,esk14_0),k5_relat_1(X1,X2))|k5_relat_1(X1,X2)!=k5_relat_1(esk11_0,esk12_0)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 18.62/18.84  cnf(c_0_31, negated_conjecture, (~r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))|~m1_subset_1(X1,esk9_0)|~r2_hidden(k4_tarski(esk13_0,X1),esk11_0)|~r2_hidden(k4_tarski(X1,esk14_0),esk12_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.62/18.84  cnf(c_0_32, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 18.62/18.84  fof(c_0_33, plain, ![X44, X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|m1_subset_1(k2_relset_1(X44,X45,X46),k1_zfmisc_1(X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 18.62/18.84  fof(c_0_34, plain, ![X47, X48, X49]:(~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k2_relset_1(X47,X48,X49)=k2_relat_1(X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 18.62/18.84  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))|r2_hidden(k4_tarski(esk13_0,esk14_0),k5_relat_1(esk11_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_30]), c_0_21]), c_0_25])])).
% 18.62/18.84  cnf(c_0_36, negated_conjecture, (~r2_hidden(k4_tarski(esk13_0,esk14_0),k5_relat_1(esk11_0,esk12_0))|~r2_hidden(k4_tarski(X1,esk14_0),esk12_0)|~r2_hidden(k4_tarski(esk13_0,X1),esk11_0)|~m1_subset_1(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_17]), c_0_22])])).
% 18.62/18.84  cnf(c_0_37, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 18.62/18.84  cnf(c_0_38, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 18.62/18.84  cnf(c_0_39, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk14_0),esk12_0)|~r2_hidden(k4_tarski(esk13_0,X1),esk11_0)|~m1_subset_1(X1,esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_35]), c_0_36])).
% 18.62/18.84  cnf(c_0_40, plain, (r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 18.62/18.84  fof(c_0_41, plain, ![X12, X13]:(~r2_hidden(X12,X13)|m1_subset_1(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 18.62/18.84  fof(c_0_42, plain, ![X9, X10, X11]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|(~r2_hidden(X11,X10)|r2_hidden(X11,X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 18.62/18.84  cnf(c_0_43, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 18.62/18.84  fof(c_0_44, plain, ![X16, X17, X18, X20, X21, X22, X23, X25]:(((~r2_hidden(X18,X17)|r2_hidden(k4_tarski(esk1_3(X16,X17,X18),X18),X16)|X17!=k2_relat_1(X16))&(~r2_hidden(k4_tarski(X21,X20),X16)|r2_hidden(X20,X17)|X17!=k2_relat_1(X16)))&((~r2_hidden(esk2_2(X22,X23),X23)|~r2_hidden(k4_tarski(X25,esk2_2(X22,X23)),X22)|X23=k2_relat_1(X22))&(r2_hidden(esk2_2(X22,X23),X23)|r2_hidden(k4_tarski(esk3_2(X22,X23),esk2_2(X22,X23)),X22)|X23=k2_relat_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 18.62/18.84  cnf(c_0_45, negated_conjecture, (X1!=k5_relat_1(X2,esk12_0)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(esk13_0,esk4_5(X2,esk12_0,X1,X3,esk14_0)),esk11_0)|~r2_hidden(k4_tarski(X3,esk14_0),X1)|~m1_subset_1(esk4_5(X2,esk12_0,X1,X3,esk14_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_21])])).
% 18.62/18.84  cnf(c_0_46, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 18.62/18.84  cnf(c_0_47, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 18.62/18.84  cnf(c_0_48, negated_conjecture, (m1_subset_1(k2_relat_1(esk11_0),k1_zfmisc_1(esk9_0))), inference(spm,[status(thm)],[c_0_43, c_0_22])).
% 18.62/18.84  cnf(c_0_49, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 18.62/18.84  cnf(c_0_50, plain, (r2_hidden(k4_tarski(X1,esk4_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 18.62/18.84  cnf(c_0_51, negated_conjecture, (X1!=k5_relat_1(X2,esk12_0)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(esk13_0,esk4_5(X2,esk12_0,X1,X3,esk14_0)),esk11_0)|~r2_hidden(esk4_5(X2,esk12_0,X1,X3,esk14_0),esk9_0)|~r2_hidden(k4_tarski(X3,esk14_0),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 18.62/18.84  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,k2_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 18.62/18.84  cnf(c_0_53, plain, (r2_hidden(esk4_5(X1,X2,X3,X4,X5),X6)|X3!=k5_relat_1(X1,X2)|X6!=k2_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X4,X5),X3)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 18.62/18.84  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk15_0,esk9_0)|r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.62/18.84  cnf(c_0_55, negated_conjecture, (X1!=k5_relat_1(esk11_0,esk12_0)|~v1_relat_1(X1)|~r2_hidden(esk4_5(esk11_0,esk12_0,X1,esk13_0,esk14_0),esk9_0)|~r2_hidden(k4_tarski(esk13_0,esk14_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_50]), c_0_25]), c_0_21])])).
% 18.62/18.84  cnf(c_0_56, negated_conjecture, (r2_hidden(esk4_5(X1,X2,X3,X4,X5),esk9_0)|k2_relat_1(esk11_0)!=k2_relat_1(X1)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X4,X5),X3)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 18.62/18.84  cnf(c_0_57, negated_conjecture, (r2_hidden(k4_tarski(esk13_0,esk14_0),k4_relset_1(esk8_0,esk9_0,esk9_0,esk10_0,esk11_0,esk12_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_20]), c_0_54]), c_0_24])).
% 18.62/18.84  cnf(c_0_58, negated_conjecture, (X1!=k5_relat_1(esk11_0,esk12_0)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(esk13_0,esk14_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_21]), c_0_25])])).
% 18.62/18.84  cnf(c_0_59, negated_conjecture, (r2_hidden(k4_tarski(esk13_0,esk14_0),k5_relat_1(esk11_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_32]), c_0_17]), c_0_22])])).
% 18.62/18.84  cnf(c_0_60, negated_conjecture, (~v1_relat_1(k5_relat_1(esk11_0,esk12_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 18.62/18.84  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_28]), c_0_21]), c_0_25])]), ['proof']).
% 18.62/18.84  # SZS output end CNFRefutation
% 18.62/18.84  # Proof object total steps             : 62
% 18.62/18.84  # Proof object clause steps            : 39
% 18.62/18.84  # Proof object formula steps           : 23
% 18.62/18.84  # Proof object conjectures             : 28
% 18.62/18.84  # Proof object clause conjectures      : 25
% 18.62/18.84  # Proof object formula conjectures     : 3
% 18.62/18.84  # Proof object initial clauses used    : 18
% 18.62/18.84  # Proof object initial formulas used   : 11
% 18.62/18.84  # Proof object generating inferences   : 21
% 18.62/18.84  # Proof object simplifying inferences  : 31
% 18.62/18.84  # Training examples: 0 positive, 0 negative
% 18.62/18.84  # Parsed axioms                        : 11
% 18.62/18.84  # Removed by relevancy pruning/SinE    : 0
% 18.62/18.84  # Initial clauses                      : 27
% 18.62/18.84  # Removed in clause preprocessing      : 0
% 18.62/18.84  # Initial clauses in saturation        : 27
% 18.62/18.84  # Processed clauses                    : 16372
% 18.62/18.84  # ...of these trivial                  : 108
% 18.62/18.84  # ...subsumed                          : 5201
% 18.62/18.84  # ...remaining for further processing  : 11063
% 18.62/18.84  # Other redundant clauses eliminated   : 0
% 18.62/18.84  # Clauses deleted for lack of memory   : 0
% 18.62/18.84  # Backward-subsumed                    : 913
% 18.62/18.84  # Backward-rewritten                   : 227
% 18.62/18.84  # Generated clauses                    : 536614
% 18.62/18.84  # ...of the previous two non-trivial   : 535932
% 18.62/18.84  # Contextual simplify-reflections      : 99
% 18.62/18.84  # Paramodulations                      : 536150
% 18.62/18.84  # Factorizations                       : 28
% 18.62/18.84  # Equation resolutions                 : 436
% 18.62/18.84  # Propositional unsat checks           : 0
% 18.62/18.84  #    Propositional check models        : 0
% 18.62/18.84  #    Propositional check unsatisfiable : 0
% 18.62/18.84  #    Propositional clauses             : 0
% 18.62/18.84  #    Propositional clauses after purity: 0
% 18.62/18.84  #    Propositional unsat core size     : 0
% 18.62/18.84  #    Propositional preprocessing time  : 0.000
% 18.62/18.84  #    Propositional encoding time       : 0.000
% 18.62/18.84  #    Propositional solver time         : 0.000
% 18.62/18.84  #    Success case prop preproc time    : 0.000
% 18.62/18.84  #    Success case prop encoding time   : 0.000
% 18.62/18.84  #    Success case prop solver time     : 0.000
% 18.62/18.84  # Current number of processed clauses  : 9896
% 18.62/18.84  #    Positive orientable unit clauses  : 9
% 18.62/18.84  #    Positive unorientable unit clauses: 0
% 18.62/18.84  #    Negative unit clauses             : 4
% 18.62/18.84  #    Non-unit-clauses                  : 9883
% 18.62/18.84  # Current number of unprocessed clauses: 515336
% 18.62/18.84  # ...number of literals in the above   : 5303267
% 18.62/18.84  # Current number of archived formulas  : 0
% 18.62/18.84  # Current number of archived clauses   : 1167
% 18.62/18.84  # Clause-clause subsumption calls (NU) : 11467893
% 18.62/18.84  # Rec. Clause-clause subsumption calls : 205569
% 18.62/18.84  # Non-unit clause-clause subsumptions  : 6193
% 18.62/18.84  # Unit Clause-clause subsumption calls : 5634
% 18.62/18.84  # Rewrite failures with RHS unbound    : 0
% 18.62/18.84  # BW rewrite match attempts            : 2
% 18.62/18.84  # BW rewrite match successes           : 2
% 18.62/18.84  # Condensation attempts                : 0
% 18.62/18.84  # Condensation successes               : 0
% 18.62/18.84  # Termbank termtop insertions          : 19148341
% 18.66/18.87  
% 18.66/18.87  # -------------------------------------------------
% 18.66/18.87  # User time                : 18.193 s
% 18.66/18.87  # System time              : 0.305 s
% 18.66/18.87  # Total time               : 18.498 s
% 18.66/18.87  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
