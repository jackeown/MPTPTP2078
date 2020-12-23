%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1026+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:00 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 179 expanded)
%              Number of clauses        :   24 (  82 expanded)
%              Number of leaves         :    3 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  129 (1327 expanded)
%              Number of equality atoms :   34 ( 465 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t121_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(c_0_3,plain,(
    ! [X1241,X1242,X1243,X1244,X1246,X1247,X1248,X1249,X1250,X1252] :
      ( ( v1_relat_1(esk168_4(X1241,X1242,X1243,X1244))
        | ~ r2_hidden(X1244,X1243)
        | X1243 != k1_funct_2(X1241,X1242) )
      & ( v1_funct_1(esk168_4(X1241,X1242,X1243,X1244))
        | ~ r2_hidden(X1244,X1243)
        | X1243 != k1_funct_2(X1241,X1242) )
      & ( X1244 = esk168_4(X1241,X1242,X1243,X1244)
        | ~ r2_hidden(X1244,X1243)
        | X1243 != k1_funct_2(X1241,X1242) )
      & ( k1_relat_1(esk168_4(X1241,X1242,X1243,X1244)) = X1241
        | ~ r2_hidden(X1244,X1243)
        | X1243 != k1_funct_2(X1241,X1242) )
      & ( r1_tarski(k2_relat_1(esk168_4(X1241,X1242,X1243,X1244)),X1242)
        | ~ r2_hidden(X1244,X1243)
        | X1243 != k1_funct_2(X1241,X1242) )
      & ( ~ v1_relat_1(X1247)
        | ~ v1_funct_1(X1247)
        | X1246 != X1247
        | k1_relat_1(X1247) != X1241
        | ~ r1_tarski(k2_relat_1(X1247),X1242)
        | r2_hidden(X1246,X1243)
        | X1243 != k1_funct_2(X1241,X1242) )
      & ( ~ r2_hidden(esk169_3(X1248,X1249,X1250),X1250)
        | ~ v1_relat_1(X1252)
        | ~ v1_funct_1(X1252)
        | esk169_3(X1248,X1249,X1250) != X1252
        | k1_relat_1(X1252) != X1248
        | ~ r1_tarski(k2_relat_1(X1252),X1249)
        | X1250 = k1_funct_2(X1248,X1249) )
      & ( v1_relat_1(esk170_3(X1248,X1249,X1250))
        | r2_hidden(esk169_3(X1248,X1249,X1250),X1250)
        | X1250 = k1_funct_2(X1248,X1249) )
      & ( v1_funct_1(esk170_3(X1248,X1249,X1250))
        | r2_hidden(esk169_3(X1248,X1249,X1250),X1250)
        | X1250 = k1_funct_2(X1248,X1249) )
      & ( esk169_3(X1248,X1249,X1250) = esk170_3(X1248,X1249,X1250)
        | r2_hidden(esk169_3(X1248,X1249,X1250),X1250)
        | X1250 = k1_funct_2(X1248,X1249) )
      & ( k1_relat_1(esk170_3(X1248,X1249,X1250)) = X1248
        | r2_hidden(esk169_3(X1248,X1249,X1250),X1250)
        | X1250 = k1_funct_2(X1248,X1249) )
      & ( r1_tarski(k2_relat_1(esk170_3(X1248,X1249,X1250)),X1249)
        | r2_hidden(esk169_3(X1248,X1249,X1250),X1250)
        | X1250 = k1_funct_2(X1248,X1249) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_5,plain,
    ( v1_funct_1(esk168_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,negated_conjecture,
    ( r2_hidden(esk3_0,k1_funct_2(esk1_0,esk2_0))
    & ( ~ v1_funct_1(esk3_0)
      | ~ v1_funct_2(esk3_0,esk1_0,esk2_0)
      | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( X1 = esk168_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( v1_funct_1(esk168_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk3_0,k1_funct_2(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( esk168_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_relat_1(esk168_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_12,plain,
    ( k1_relat_1(esk168_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_13,plain,
    ( v1_relat_1(esk168_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk168_4(esk1_0,esk2_0,k1_funct_2(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( esk168_4(esk1_0,esk2_0,k1_funct_2(esk1_0,esk2_0),esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_9])).

fof(c_0_16,plain,(
    ! [X158,X159] :
      ( ( v1_funct_1(X159)
        | ~ r1_tarski(k2_relat_1(X159),X158)
        | ~ v1_relat_1(X159)
        | ~ v1_funct_1(X159) )
      & ( v1_funct_2(X159,k1_relat_1(X159),X158)
        | ~ r1_tarski(k2_relat_1(X159),X158)
        | ~ v1_relat_1(X159)
        | ~ v1_funct_1(X159) )
      & ( m1_subset_1(X159,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X159),X158)))
        | ~ r1_tarski(k2_relat_1(X159),X158)
        | ~ v1_relat_1(X159)
        | ~ v1_funct_1(X159) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_relat_1(esk168_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_relat_1(esk168_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_relat_1(esk168_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_funct_1(esk3_0)
    | ~ v1_funct_2(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_9]),c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_9]),c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_9]),c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_21]),c_0_25])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_24]),c_0_21]),c_0_25])]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
