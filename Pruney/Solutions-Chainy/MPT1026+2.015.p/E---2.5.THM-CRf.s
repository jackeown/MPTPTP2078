%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:46 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 758 expanded)
%              Number of clauses        :  102 ( 386 expanded)
%              Number of leaves         :   22 ( 169 expanded)
%              Depth                    :   17
%              Number of atoms          :  490 (5557 expanded)
%              Number of equality atoms :  105 (2030 expanded)
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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(c_0_22,plain,(
    ! [X57,X58,X59,X60,X62,X63,X64,X65,X66,X68] :
      ( ( v1_relat_1(esk8_4(X57,X58,X59,X60))
        | ~ r2_hidden(X60,X59)
        | X59 != k1_funct_2(X57,X58) )
      & ( v1_funct_1(esk8_4(X57,X58,X59,X60))
        | ~ r2_hidden(X60,X59)
        | X59 != k1_funct_2(X57,X58) )
      & ( X60 = esk8_4(X57,X58,X59,X60)
        | ~ r2_hidden(X60,X59)
        | X59 != k1_funct_2(X57,X58) )
      & ( k1_relat_1(esk8_4(X57,X58,X59,X60)) = X57
        | ~ r2_hidden(X60,X59)
        | X59 != k1_funct_2(X57,X58) )
      & ( r1_tarski(k2_relat_1(esk8_4(X57,X58,X59,X60)),X58)
        | ~ r2_hidden(X60,X59)
        | X59 != k1_funct_2(X57,X58) )
      & ( ~ v1_relat_1(X63)
        | ~ v1_funct_1(X63)
        | X62 != X63
        | k1_relat_1(X63) != X57
        | ~ r1_tarski(k2_relat_1(X63),X58)
        | r2_hidden(X62,X59)
        | X59 != k1_funct_2(X57,X58) )
      & ( ~ r2_hidden(esk9_3(X64,X65,X66),X66)
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68)
        | esk9_3(X64,X65,X66) != X68
        | k1_relat_1(X68) != X64
        | ~ r1_tarski(k2_relat_1(X68),X65)
        | X66 = k1_funct_2(X64,X65) )
      & ( v1_relat_1(esk10_3(X64,X65,X66))
        | r2_hidden(esk9_3(X64,X65,X66),X66)
        | X66 = k1_funct_2(X64,X65) )
      & ( v1_funct_1(esk10_3(X64,X65,X66))
        | r2_hidden(esk9_3(X64,X65,X66),X66)
        | X66 = k1_funct_2(X64,X65) )
      & ( esk9_3(X64,X65,X66) = esk10_3(X64,X65,X66)
        | r2_hidden(esk9_3(X64,X65,X66),X66)
        | X66 = k1_funct_2(X64,X65) )
      & ( k1_relat_1(esk10_3(X64,X65,X66)) = X64
        | r2_hidden(esk9_3(X64,X65,X66),X66)
        | X66 = k1_funct_2(X64,X65) )
      & ( r1_tarski(k2_relat_1(esk10_3(X64,X65,X66)),X65)
        | r2_hidden(esk9_3(X64,X65,X66),X66)
        | X66 = k1_funct_2(X64,X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_23,plain,
    ( k1_relat_1(esk8_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_24,plain,
    ( X1 = esk8_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_26,plain,
    ( v1_funct_1(esk8_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( v1_relat_1(esk8_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k1_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( esk8_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_24])).

fof(c_0_30,negated_conjecture,
    ( r2_hidden(esk13_0,k1_funct_2(esk11_0,esk12_0))
    & ( ~ v1_funct_1(esk13_0)
      | ~ v1_funct_2(esk13_0,esk11_0,esk12_0)
      | ~ m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_31,plain,
    ( v1_funct_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( v1_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X20,X21] :
      ( ( k2_zfmisc_1(X20,X21) != k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k2_zfmisc_1(X20,X21) = k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k2_zfmisc_1(X20,X21) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_34,plain,(
    ! [X35,X36,X37,X39,X40,X41,X43] :
      ( ( r2_hidden(esk5_3(X35,X36,X37),k1_relat_1(X35))
        | ~ r2_hidden(X37,X36)
        | X36 != k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( X37 = k1_funct_1(X35,esk5_3(X35,X36,X37))
        | ~ r2_hidden(X37,X36)
        | X36 != k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(X40,k1_relat_1(X35))
        | X39 != k1_funct_1(X35,X40)
        | r2_hidden(X39,X36)
        | X36 != k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(esk6_2(X35,X41),X41)
        | ~ r2_hidden(X43,k1_relat_1(X35))
        | esk6_2(X35,X41) != k1_funct_1(X35,X43)
        | X41 = k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( r2_hidden(esk7_2(X35,X41),k1_relat_1(X35))
        | r2_hidden(esk6_2(X35,X41),X41)
        | X41 = k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( esk6_2(X35,X41) = k1_funct_1(X35,esk7_2(X35,X41))
        | r2_hidden(esk6_2(X35,X41),X41)
        | X41 = k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_35,plain,(
    ! [X71] :
      ( ( v1_funct_1(X71)
        | ~ v1_relat_1(X71)
        | ~ v1_funct_1(X71) )
      & ( v1_funct_2(X71,k1_relat_1(X71),k2_relat_1(X71))
        | ~ v1_relat_1(X71)
        | ~ v1_funct_1(X71) )
      & ( m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X71),k2_relat_1(X71))))
        | ~ v1_relat_1(X71)
        | ~ v1_funct_1(X71) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_36,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk13_0,k1_funct_2(esk11_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

fof(c_0_40,plain,(
    ! [X45,X46,X47] :
      ( ~ v1_xboole_0(X45)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X45)))
      | v1_xboole_0(X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_42,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_44,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_45,plain,(
    ! [X24] : m1_subset_1(esk4_1(X24),X24) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_46,plain,(
    ! [X22,X23] : ~ r2_hidden(X22,k2_zfmisc_1(X22,X23)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(esk13_0) = esk11_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk13_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk13_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_54,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_55,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_56,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_61,plain,(
    ! [X34] :
      ( ( k1_relat_1(X34) != k1_xboole_0
        | k2_relat_1(X34) = k1_xboole_0
        | ~ v1_relat_1(X34) )
      & ( k2_relat_1(X34) != k1_xboole_0
        | k1_relat_1(X34) = k1_xboole_0
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_63,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,k2_relat_1(esk13_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_65,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_67,plain,(
    ! [X16] :
      ( X16 = k1_xboole_0
      | r2_hidden(esk3_1(X16),X16) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_71,plain,
    ( r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_52])).

fof(c_0_74,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X32))
      | ~ v1_xboole_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_75,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,negated_conjecture,
    ( v1_xboole_0(esk13_0)
    | ~ v1_xboole_0(k2_relat_1(esk13_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_64])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_78,plain,(
    ! [X70] :
      ( v1_partfun1(k6_partfun1(X70),X70)
      & m1_subset_1(k6_partfun1(X70),k1_zfmisc_1(k2_zfmisc_1(X70,X70))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_66])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_82,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_83,plain,
    ( k2_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_84,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_85,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | r1_tarski(X33,k2_zfmisc_1(k1_relat_1(X33),k2_relat_1(X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_75])).

cnf(c_0_87,negated_conjecture,
    ( v1_xboole_0(esk13_0)
    | ~ r1_tarski(k2_relat_1(esk13_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_88,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_89,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_79])).

cnf(c_0_90,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(esk11_0)
    | ~ v1_xboole_0(k2_relat_1(esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_92,plain,
    ( v1_xboole_0(k2_relat_1(X1))
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_70])).

fof(c_0_93,plain,(
    ! [X48,X49,X50] :
      ( ~ v1_relat_1(X50)
      | ~ r1_tarski(k1_relat_1(X50),X48)
      | ~ r1_tarski(k2_relat_1(X50),X49)
      | m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_94,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_66])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_96,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk13_0,X1)
    | ~ r1_tarski(k2_relat_1(esk13_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_98,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_75])).

cnf(c_0_99,plain,
    ( ~ r2_hidden(X1,k6_partfun1(X2))
    | ~ v1_xboole_0(k2_zfmisc_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_88])).

cnf(c_0_100,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(esk11_0)
    | k2_relat_1(esk13_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_49]),c_0_50])])).

cnf(c_0_102,negated_conjecture,
    ( ~ v1_funct_1(esk13_0)
    | ~ v1_funct_2(esk13_0,esk11_0,esk12_0)
    | ~ m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_103,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_104,plain,
    ( r1_tarski(k2_relat_1(esk8_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_105,plain,(
    ! [X51,X52,X53] :
      ( ( v1_funct_1(X53)
        | ~ v1_funct_1(X53)
        | ~ v1_partfun1(X53,X51)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v1_funct_2(X53,X51,X52)
        | ~ v1_funct_1(X53)
        | ~ v1_partfun1(X53,X51)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_106,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1)
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_107,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_96])).

cnf(c_0_108,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(esk13_0,X1)
    | k2_relat_1(esk13_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_49]),c_0_50])])).

cnf(c_0_110,plain,
    ( r1_tarski(k6_partfun1(X1),X2)
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_75])).

cnf(c_0_111,negated_conjecture,
    ( k2_zfmisc_1(X1,esk11_0) = k1_xboole_0
    | k2_relat_1(esk13_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_112,negated_conjecture,
    ( ~ v1_funct_2(esk13_0,esk11_0,esk12_0)
    | ~ v1_funct_1(esk13_0)
    | ~ v1_relat_1(esk13_0)
    | ~ r1_tarski(k1_relat_1(esk13_0),esk11_0)
    | ~ r1_tarski(k2_relat_1(esk13_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_113,plain,
    ( r1_tarski(k2_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_104])).

cnf(c_0_114,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_115,plain,
    ( k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_72]),c_0_107]),c_0_53])])).

cnf(c_0_116,negated_conjecture,
    ( X1 = esk13_0
    | k2_relat_1(esk13_0) != k1_xboole_0
    | ~ r1_tarski(X1,esk13_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k6_partfun1(esk11_0),X1)
    | k2_relat_1(esk13_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_53])])).

cnf(c_0_118,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_71])).

cnf(c_0_119,negated_conjecture,
    ( ~ v1_funct_2(esk13_0,esk11_0,esk12_0)
    | ~ r1_tarski(k1_relat_1(esk13_0),esk11_0)
    | ~ r1_tarski(k2_relat_1(esk13_0),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_49])]),c_0_50])])).

cnf(c_0_120,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_29])).

cnf(c_0_121,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_66])).

cnf(c_0_122,plain,
    ( r1_tarski(X1,X2)
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_115,c_0_75])).

cnf(c_0_123,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_124,negated_conjecture,
    ( k6_partfun1(esk11_0) = esk13_0
    | k2_relat_1(esk13_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_125,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_114,c_0_103])).

fof(c_0_126,plain,(
    ! [X54,X55,X56] :
      ( ( v1_funct_1(X56)
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
        | v1_xboole_0(X55) )
      & ( v1_partfun1(X56,X54)
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
        | v1_xboole_0(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_127,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_128,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_79])).

cnf(c_0_129,negated_conjecture,
    ( ~ v1_funct_2(esk13_0,esk11_0,esk12_0)
    | ~ r1_tarski(k2_relat_1(esk13_0),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_48]),c_0_81])])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk13_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_37])).

cnf(c_0_131,plain,
    ( v1_funct_2(X1,X2,X3)
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_132,negated_conjecture,
    ( v1_partfun1(esk13_0,esk11_0)
    | k2_relat_1(esk13_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_133,negated_conjecture,
    ( v1_funct_2(esk13_0,X1,X2)
    | ~ v1_partfun1(esk13_0,X1)
    | ~ r1_tarski(k2_relat_1(esk13_0),X2)
    | ~ r1_tarski(esk11_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_134,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_135,negated_conjecture,
    ( v1_funct_2(esk13_0,esk11_0,k2_relat_1(esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_136,plain,
    ( k2_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3)) = k1_xboole_0
    | ~ r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_28]),c_0_32]),c_0_31])).

cnf(c_0_137,negated_conjecture,
    ( ~ v1_funct_2(esk13_0,esk11_0,esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_130])])).

cnf(c_0_138,negated_conjecture,
    ( v1_funct_2(esk13_0,esk11_0,X1)
    | k2_relat_1(esk13_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_49]),c_0_50])])).

cnf(c_0_139,negated_conjecture,
    ( v1_funct_2(esk13_0,X1,esk12_0)
    | ~ v1_partfun1(esk13_0,X1)
    | ~ r1_tarski(esk11_0,X1) ),
    inference(spm,[status(thm)],[c_0_133,c_0_130])).

cnf(c_0_140,negated_conjecture,
    ( v1_partfun1(esk13_0,esk11_0)
    | v1_xboole_0(k2_relat_1(esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_64]),c_0_135]),c_0_49])])).

cnf(c_0_141,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_funct_2(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_136,c_0_29])).

cnf(c_0_142,negated_conjecture,
    ( k2_relat_1(esk13_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_143,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk13_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_81])]),c_0_137])).

cnf(c_0_144,negated_conjecture,
    ( ~ v1_xboole_0(esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_37]),c_0_142])).

cnf(c_0_145,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_143])]),c_0_144]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.77/0.95  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.77/0.95  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.77/0.95  #
% 0.77/0.95  # Preprocessing time       : 0.029 s
% 0.77/0.95  # Presaturation interreduction done
% 0.77/0.95  
% 0.77/0.95  # Proof found!
% 0.77/0.95  # SZS status Theorem
% 0.77/0.95  # SZS output start CNFRefutation
% 0.77/0.95  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.77/0.95  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.77/0.95  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.77/0.95  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.77/0.95  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.77/0.95  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.77/0.95  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.77/0.95  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.77/0.95  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.77/0.95  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.77/0.95  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.77/0.95  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.77/0.95  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.77/0.95  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.77/0.95  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.77/0.95  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.77/0.95  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.77/0.95  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.77/0.95  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 0.77/0.95  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.77/0.95  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.77/0.95  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.77/0.95  fof(c_0_22, plain, ![X57, X58, X59, X60, X62, X63, X64, X65, X66, X68]:(((((((v1_relat_1(esk8_4(X57,X58,X59,X60))|~r2_hidden(X60,X59)|X59!=k1_funct_2(X57,X58))&(v1_funct_1(esk8_4(X57,X58,X59,X60))|~r2_hidden(X60,X59)|X59!=k1_funct_2(X57,X58)))&(X60=esk8_4(X57,X58,X59,X60)|~r2_hidden(X60,X59)|X59!=k1_funct_2(X57,X58)))&(k1_relat_1(esk8_4(X57,X58,X59,X60))=X57|~r2_hidden(X60,X59)|X59!=k1_funct_2(X57,X58)))&(r1_tarski(k2_relat_1(esk8_4(X57,X58,X59,X60)),X58)|~r2_hidden(X60,X59)|X59!=k1_funct_2(X57,X58)))&(~v1_relat_1(X63)|~v1_funct_1(X63)|X62!=X63|k1_relat_1(X63)!=X57|~r1_tarski(k2_relat_1(X63),X58)|r2_hidden(X62,X59)|X59!=k1_funct_2(X57,X58)))&((~r2_hidden(esk9_3(X64,X65,X66),X66)|(~v1_relat_1(X68)|~v1_funct_1(X68)|esk9_3(X64,X65,X66)!=X68|k1_relat_1(X68)!=X64|~r1_tarski(k2_relat_1(X68),X65))|X66=k1_funct_2(X64,X65))&(((((v1_relat_1(esk10_3(X64,X65,X66))|r2_hidden(esk9_3(X64,X65,X66),X66)|X66=k1_funct_2(X64,X65))&(v1_funct_1(esk10_3(X64,X65,X66))|r2_hidden(esk9_3(X64,X65,X66),X66)|X66=k1_funct_2(X64,X65)))&(esk9_3(X64,X65,X66)=esk10_3(X64,X65,X66)|r2_hidden(esk9_3(X64,X65,X66),X66)|X66=k1_funct_2(X64,X65)))&(k1_relat_1(esk10_3(X64,X65,X66))=X64|r2_hidden(esk9_3(X64,X65,X66),X66)|X66=k1_funct_2(X64,X65)))&(r1_tarski(k2_relat_1(esk10_3(X64,X65,X66)),X65)|r2_hidden(esk9_3(X64,X65,X66),X66)|X66=k1_funct_2(X64,X65))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.77/0.95  cnf(c_0_23, plain, (k1_relat_1(esk8_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.77/0.95  cnf(c_0_24, plain, (X1=esk8_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.77/0.95  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 0.77/0.95  cnf(c_0_26, plain, (v1_funct_1(esk8_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.77/0.95  cnf(c_0_27, plain, (v1_relat_1(esk8_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.77/0.95  cnf(c_0_28, plain, (k1_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.77/0.95  cnf(c_0_29, plain, (esk8_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_24])).
% 0.77/0.95  fof(c_0_30, negated_conjecture, (r2_hidden(esk13_0,k1_funct_2(esk11_0,esk12_0))&(~v1_funct_1(esk13_0)|~v1_funct_2(esk13_0,esk11_0,esk12_0)|~m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.77/0.95  cnf(c_0_31, plain, (v1_funct_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_26])).
% 0.77/0.95  cnf(c_0_32, plain, (v1_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_27])).
% 0.77/0.95  fof(c_0_33, plain, ![X20, X21]:((k2_zfmisc_1(X20,X21)!=k1_xboole_0|(X20=k1_xboole_0|X21=k1_xboole_0))&((X20!=k1_xboole_0|k2_zfmisc_1(X20,X21)=k1_xboole_0)&(X21!=k1_xboole_0|k2_zfmisc_1(X20,X21)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.77/0.95  fof(c_0_34, plain, ![X35, X36, X37, X39, X40, X41, X43]:((((r2_hidden(esk5_3(X35,X36,X37),k1_relat_1(X35))|~r2_hidden(X37,X36)|X36!=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(X37=k1_funct_1(X35,esk5_3(X35,X36,X37))|~r2_hidden(X37,X36)|X36!=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(~r2_hidden(X40,k1_relat_1(X35))|X39!=k1_funct_1(X35,X40)|r2_hidden(X39,X36)|X36!=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&((~r2_hidden(esk6_2(X35,X41),X41)|(~r2_hidden(X43,k1_relat_1(X35))|esk6_2(X35,X41)!=k1_funct_1(X35,X43))|X41=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&((r2_hidden(esk7_2(X35,X41),k1_relat_1(X35))|r2_hidden(esk6_2(X35,X41),X41)|X41=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(esk6_2(X35,X41)=k1_funct_1(X35,esk7_2(X35,X41))|r2_hidden(esk6_2(X35,X41),X41)|X41=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.77/0.95  fof(c_0_35, plain, ![X71]:(((v1_funct_1(X71)|(~v1_relat_1(X71)|~v1_funct_1(X71)))&(v1_funct_2(X71,k1_relat_1(X71),k2_relat_1(X71))|(~v1_relat_1(X71)|~v1_funct_1(X71))))&(m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X71),k2_relat_1(X71))))|(~v1_relat_1(X71)|~v1_funct_1(X71)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.77/0.95  cnf(c_0_36, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.77/0.95  cnf(c_0_37, negated_conjecture, (r2_hidden(esk13_0,k1_funct_2(esk11_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.77/0.95  cnf(c_0_38, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.77/0.95  cnf(c_0_39, plain, (v1_relat_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 0.77/0.95  fof(c_0_40, plain, ![X45, X46, X47]:(~v1_xboole_0(X45)|(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X45)))|v1_xboole_0(X47))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.77/0.95  cnf(c_0_41, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.77/0.95  fof(c_0_42, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.77/0.95  cnf(c_0_43, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.77/0.95  fof(c_0_44, plain, ![X26, X27]:(~m1_subset_1(X26,X27)|(v1_xboole_0(X27)|r2_hidden(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.77/0.95  fof(c_0_45, plain, ![X24]:m1_subset_1(esk4_1(X24),X24), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.77/0.95  fof(c_0_46, plain, ![X22, X23]:~r2_hidden(X22,k2_zfmisc_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.77/0.95  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.77/0.95  cnf(c_0_48, negated_conjecture, (k1_relat_1(esk13_0)=esk11_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.77/0.95  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk13_0)), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.77/0.95  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk13_0)), inference(spm,[status(thm)],[c_0_39, c_0_37])).
% 0.77/0.95  cnf(c_0_51, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.77/0.95  cnf(c_0_52, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_41])).
% 0.77/0.95  cnf(c_0_53, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.77/0.95  fof(c_0_54, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.77/0.95  fof(c_0_55, plain, ![X18, X19]:(((r1_tarski(X18,X19)|X18!=X19)&(r1_tarski(X19,X18)|X18!=X19))&(~r1_tarski(X18,X19)|~r1_tarski(X19,X18)|X18=X19)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.77/0.95  cnf(c_0_56, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.77/0.95  cnf(c_0_57, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).
% 0.77/0.95  cnf(c_0_58, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.77/0.95  cnf(c_0_59, plain, (m1_subset_1(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.77/0.95  cnf(c_0_60, plain, (r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.77/0.95  fof(c_0_61, plain, ![X34]:((k1_relat_1(X34)!=k1_xboole_0|k2_relat_1(X34)=k1_xboole_0|~v1_relat_1(X34))&(k2_relat_1(X34)!=k1_xboole_0|k1_relat_1(X34)=k1_xboole_0|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.77/0.95  cnf(c_0_62, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.77/0.95  fof(c_0_63, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.77/0.95  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,k2_relat_1(esk13_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50])])).
% 0.77/0.95  cnf(c_0_65, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.77/0.95  cnf(c_0_66, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.77/0.95  fof(c_0_67, plain, ![X16]:(X16=k1_xboole_0|r2_hidden(esk3_1(X16),X16)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.77/0.95  cnf(c_0_68, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.77/0.95  cnf(c_0_69, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.77/0.95  cnf(c_0_70, plain, (r2_hidden(esk4_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.77/0.95  cnf(c_0_71, plain, (r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_60])).
% 0.77/0.95  cnf(c_0_72, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.77/0.95  cnf(c_0_73, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_52])).
% 0.77/0.95  fof(c_0_74, plain, ![X30, X31, X32]:(~r2_hidden(X30,X31)|~m1_subset_1(X31,k1_zfmisc_1(X32))|~v1_xboole_0(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.77/0.95  cnf(c_0_75, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.77/0.95  cnf(c_0_76, negated_conjecture, (v1_xboole_0(esk13_0)|~v1_xboole_0(k2_relat_1(esk13_0))), inference(spm,[status(thm)],[c_0_51, c_0_64])).
% 0.77/0.95  cnf(c_0_77, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.77/0.95  fof(c_0_78, plain, ![X70]:(v1_partfun1(k6_partfun1(X70),X70)&m1_subset_1(k6_partfun1(X70),k1_zfmisc_1(k2_zfmisc_1(X70,X70)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.77/0.95  cnf(c_0_79, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.77/0.95  cnf(c_0_80, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_51, c_0_66])).
% 0.77/0.95  cnf(c_0_81, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_68])).
% 0.77/0.95  cnf(c_0_82, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.77/0.95  cnf(c_0_83, plain, (k2_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 0.77/0.95  cnf(c_0_84, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.77/0.95  fof(c_0_85, plain, ![X33]:(~v1_relat_1(X33)|r1_tarski(X33,k2_zfmisc_1(k1_relat_1(X33),k2_relat_1(X33)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.77/0.95  cnf(c_0_86, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_56, c_0_75])).
% 0.77/0.95  cnf(c_0_87, negated_conjecture, (v1_xboole_0(esk13_0)|~r1_tarski(k2_relat_1(esk13_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.77/0.95  cnf(c_0_88, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.77/0.95  cnf(c_0_89, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_56, c_0_79])).
% 0.77/0.95  cnf(c_0_90, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.77/0.95  cnf(c_0_91, negated_conjecture, (v1_xboole_0(esk11_0)|~v1_xboole_0(k2_relat_1(esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_48]), c_0_49]), c_0_50])])).
% 0.77/0.95  cnf(c_0_92, plain, (v1_xboole_0(k2_relat_1(X1))|k2_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_83, c_0_70])).
% 0.77/0.95  fof(c_0_93, plain, ![X48, X49, X50]:(~v1_relat_1(X50)|(~r1_tarski(k1_relat_1(X50),X48)|~r1_tarski(k2_relat_1(X50),X49)|m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.77/0.95  cnf(c_0_94, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_84, c_0_66])).
% 0.77/0.95  cnf(c_0_95, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.77/0.95  cnf(c_0_96, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.77/0.95  cnf(c_0_97, negated_conjecture, (r1_tarski(esk13_0,X1)|~r1_tarski(k2_relat_1(esk13_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.77/0.95  cnf(c_0_98, plain, (r1_tarski(k2_relat_1(X1),X2)|k2_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_83, c_0_75])).
% 0.77/0.95  cnf(c_0_99, plain, (~r2_hidden(X1,k6_partfun1(X2))|~v1_xboole_0(k2_zfmisc_1(X2,X2))), inference(spm,[status(thm)],[c_0_84, c_0_88])).
% 0.77/0.95  cnf(c_0_100, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.77/0.95  cnf(c_0_101, negated_conjecture, (v1_xboole_0(esk11_0)|k2_relat_1(esk13_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_49]), c_0_50])])).
% 0.77/0.95  cnf(c_0_102, negated_conjecture, (~v1_funct_1(esk13_0)|~v1_funct_2(esk13_0,esk11_0,esk12_0)|~m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.77/0.95  cnf(c_0_103, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.77/0.95  cnf(c_0_104, plain, (r1_tarski(k2_relat_1(esk8_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.77/0.95  fof(c_0_105, plain, ![X51, X52, X53]:((v1_funct_1(X53)|(~v1_funct_1(X53)|~v1_partfun1(X53,X51))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(v1_funct_2(X53,X51,X52)|(~v1_funct_1(X53)|~v1_partfun1(X53,X51))|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.77/0.95  cnf(c_0_106, plain, (~v1_relat_1(X1)|~r2_hidden(X2,X1)|~v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.77/0.95  cnf(c_0_107, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_96])).
% 0.77/0.95  cnf(c_0_108, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.77/0.95  cnf(c_0_109, negated_conjecture, (r1_tarski(esk13_0,X1)|k2_relat_1(esk13_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_49]), c_0_50])])).
% 0.77/0.95  cnf(c_0_110, plain, (r1_tarski(k6_partfun1(X1),X2)|~v1_xboole_0(k2_zfmisc_1(X1,X1))), inference(spm,[status(thm)],[c_0_99, c_0_75])).
% 0.77/0.95  cnf(c_0_111, negated_conjecture, (k2_zfmisc_1(X1,esk11_0)=k1_xboole_0|k2_relat_1(esk13_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.77/0.95  cnf(c_0_112, negated_conjecture, (~v1_funct_2(esk13_0,esk11_0,esk12_0)|~v1_funct_1(esk13_0)|~v1_relat_1(esk13_0)|~r1_tarski(k1_relat_1(esk13_0),esk11_0)|~r1_tarski(k2_relat_1(esk13_0),esk12_0)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.77/0.95  cnf(c_0_113, plain, (r1_tarski(k2_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_104])).
% 0.77/0.95  cnf(c_0_114, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.77/0.95  cnf(c_0_115, plain, (k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_72]), c_0_107]), c_0_53])])).
% 0.77/0.95  cnf(c_0_116, negated_conjecture, (X1=esk13_0|k2_relat_1(esk13_0)!=k1_xboole_0|~r1_tarski(X1,esk13_0)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.77/0.95  cnf(c_0_117, negated_conjecture, (r1_tarski(k6_partfun1(esk11_0),X1)|k2_relat_1(esk13_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_53])])).
% 0.77/0.95  cnf(c_0_118, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_71])).
% 0.77/0.95  cnf(c_0_119, negated_conjecture, (~v1_funct_2(esk13_0,esk11_0,esk12_0)|~r1_tarski(k1_relat_1(esk13_0),esk11_0)|~r1_tarski(k2_relat_1(esk13_0),esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_49])]), c_0_50])])).
% 0.77/0.95  cnf(c_0_120, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(spm,[status(thm)],[c_0_113, c_0_29])).
% 0.77/0.95  cnf(c_0_121, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_114, c_0_66])).
% 0.77/0.95  cnf(c_0_122, plain, (r1_tarski(X1,X2)|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_115, c_0_75])).
% 0.77/0.95  cnf(c_0_123, plain, (v1_partfun1(k6_partfun1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.77/0.95  cnf(c_0_124, negated_conjecture, (k6_partfun1(esk11_0)=esk13_0|k2_relat_1(esk13_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 0.77/0.95  cnf(c_0_125, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_114, c_0_103])).
% 0.77/0.95  fof(c_0_126, plain, ![X54, X55, X56]:((v1_funct_1(X56)|(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X55))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|v1_xboole_0(X55))&(v1_partfun1(X56,X54)|(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X55))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|v1_xboole_0(X55))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.77/0.95  cnf(c_0_127, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.77/0.95  cnf(c_0_128, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_118, c_0_79])).
% 0.77/0.95  cnf(c_0_129, negated_conjecture, (~v1_funct_2(esk13_0,esk11_0,esk12_0)|~r1_tarski(k2_relat_1(esk13_0),esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_48]), c_0_81])])).
% 0.77/0.95  cnf(c_0_130, negated_conjecture, (r1_tarski(k2_relat_1(esk13_0),esk12_0)), inference(spm,[status(thm)],[c_0_120, c_0_37])).
% 0.77/0.95  cnf(c_0_131, plain, (v1_funct_2(X1,X2,X3)|k2_relat_1(X1)!=k1_xboole_0|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 0.77/0.95  cnf(c_0_132, negated_conjecture, (v1_partfun1(esk13_0,esk11_0)|k2_relat_1(esk13_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 0.77/0.95  cnf(c_0_133, negated_conjecture, (v1_funct_2(esk13_0,X1,X2)|~v1_partfun1(esk13_0,X1)|~r1_tarski(k2_relat_1(esk13_0),X2)|~r1_tarski(esk11_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_48]), c_0_49]), c_0_50])])).
% 0.77/0.95  cnf(c_0_134, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_126])).
% 0.77/0.95  cnf(c_0_135, negated_conjecture, (v1_funct_2(esk13_0,esk11_0,k2_relat_1(esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_48]), c_0_49]), c_0_50])])).
% 0.77/0.95  cnf(c_0_136, plain, (k2_relat_1(esk8_4(X1,X2,k1_funct_2(X1,X2),X3))=k1_xboole_0|~r2_hidden(X3,k1_funct_2(X1,X2))|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_28]), c_0_32]), c_0_31])).
% 0.77/0.95  cnf(c_0_137, negated_conjecture, (~v1_funct_2(esk13_0,esk11_0,esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_130])])).
% 0.77/0.95  cnf(c_0_138, negated_conjecture, (v1_funct_2(esk13_0,esk11_0,X1)|k2_relat_1(esk13_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_49]), c_0_50])])).
% 0.77/0.95  cnf(c_0_139, negated_conjecture, (v1_funct_2(esk13_0,X1,esk12_0)|~v1_partfun1(esk13_0,X1)|~r1_tarski(esk11_0,X1)), inference(spm,[status(thm)],[c_0_133, c_0_130])).
% 0.77/0.95  cnf(c_0_140, negated_conjecture, (v1_partfun1(esk13_0,esk11_0)|v1_xboole_0(k2_relat_1(esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_64]), c_0_135]), c_0_49])])).
% 0.77/0.95  cnf(c_0_141, plain, (k2_relat_1(X1)=k1_xboole_0|~r2_hidden(X1,k1_funct_2(X2,X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_136, c_0_29])).
% 0.77/0.95  cnf(c_0_142, negated_conjecture, (k2_relat_1(esk13_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 0.77/0.95  cnf(c_0_143, negated_conjecture, (v1_xboole_0(k2_relat_1(esk13_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_81])]), c_0_137])).
% 0.77/0.95  cnf(c_0_144, negated_conjecture, (~v1_xboole_0(esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_37]), c_0_142])).
% 0.77/0.95  cnf(c_0_145, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_143])]), c_0_144]), ['proof']).
% 0.77/0.95  # SZS output end CNFRefutation
% 0.77/0.95  # Proof object total steps             : 146
% 0.77/0.95  # Proof object clause steps            : 102
% 0.77/0.95  # Proof object formula steps           : 44
% 0.77/0.95  # Proof object conjectures             : 34
% 0.77/0.95  # Proof object clause conjectures      : 31
% 0.77/0.95  # Proof object formula conjectures     : 3
% 0.77/0.95  # Proof object initial clauses used    : 32
% 0.77/0.95  # Proof object initial formulas used   : 22
% 0.77/0.95  # Proof object generating inferences   : 56
% 0.77/0.95  # Proof object simplifying inferences  : 61
% 0.77/0.95  # Training examples: 0 positive, 0 negative
% 0.77/0.95  # Parsed axioms                        : 22
% 0.77/0.95  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.95  # Initial clauses                      : 53
% 0.77/0.95  # Removed in clause preprocessing      : 3
% 0.77/0.95  # Initial clauses in saturation        : 50
% 0.77/0.95  # Processed clauses                    : 9060
% 0.77/0.95  # ...of these trivial                  : 39
% 0.77/0.95  # ...subsumed                          : 7488
% 0.77/0.95  # ...remaining for further processing  : 1533
% 0.77/0.95  # Other redundant clauses eliminated   : 72
% 0.77/0.95  # Clauses deleted for lack of memory   : 0
% 0.77/0.95  # Backward-subsumed                    : 150
% 0.77/0.95  # Backward-rewritten                   : 90
% 0.77/0.95  # Generated clauses                    : 37810
% 0.77/0.95  # ...of the previous two non-trivial   : 32688
% 0.77/0.95  # Contextual simplify-reflections      : 115
% 0.77/0.95  # Paramodulations                      : 37728
% 0.77/0.95  # Factorizations                       : 0
% 0.77/0.95  # Equation resolutions                 : 72
% 0.77/0.95  # Propositional unsat checks           : 0
% 0.77/0.95  #    Propositional check models        : 0
% 0.77/0.95  #    Propositional check unsatisfiable : 0
% 0.77/0.95  #    Propositional clauses             : 0
% 0.77/0.95  #    Propositional clauses after purity: 0
% 0.77/0.95  #    Propositional unsat core size     : 0
% 0.77/0.95  #    Propositional preprocessing time  : 0.000
% 0.77/0.95  #    Propositional encoding time       : 0.000
% 0.77/0.95  #    Propositional solver time         : 0.000
% 0.77/0.95  #    Success case prop preproc time    : 0.000
% 0.77/0.95  #    Success case prop encoding time   : 0.000
% 0.77/0.95  #    Success case prop solver time     : 0.000
% 0.77/0.95  # Current number of processed clauses  : 1217
% 0.77/0.95  #    Positive orientable unit clauses  : 29
% 0.77/0.95  #    Positive unorientable unit clauses: 0
% 0.77/0.95  #    Negative unit clauses             : 13
% 0.77/0.95  #    Non-unit-clauses                  : 1175
% 0.77/0.95  # Current number of unprocessed clauses: 23219
% 0.77/0.95  # ...number of literals in the above   : 97742
% 0.77/0.95  # Current number of archived formulas  : 0
% 0.77/0.95  # Current number of archived clauses   : 302
% 0.77/0.95  # Clause-clause subsumption calls (NU) : 218580
% 0.77/0.95  # Rec. Clause-clause subsumption calls : 119984
% 0.77/0.95  # Non-unit clause-clause subsumptions  : 4717
% 0.77/0.95  # Unit Clause-clause subsumption calls : 2342
% 0.77/0.95  # Rewrite failures with RHS unbound    : 0
% 0.77/0.95  # BW rewrite match attempts            : 12
% 0.77/0.95  # BW rewrite match successes           : 10
% 0.77/0.95  # Condensation attempts                : 0
% 0.77/0.95  # Condensation successes               : 0
% 0.77/0.95  # Termbank termtop insertions          : 504979
% 0.77/0.95  
% 0.77/0.95  # -------------------------------------------------
% 0.77/0.95  # User time                : 0.601 s
% 0.77/0.95  # System time              : 0.013 s
% 0.77/0.95  # Total time               : 0.614 s
% 0.77/0.95  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
