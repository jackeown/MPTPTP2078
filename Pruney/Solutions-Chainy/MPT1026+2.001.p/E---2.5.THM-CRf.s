%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:43 EST 2020

% Result     : Theorem 6.32s
% Output     : CNFRefutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :  130 (6988 expanded)
%              Number of clauses        :   99 (3332 expanded)
%              Number of leaves         :   15 (1719 expanded)
%              Depth                    :   32
%              Number of atoms          :  395 (28529 expanded)
%              Number of equality atoms :   81 (7796 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(t121_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(c_0_15,plain,(
    ! [X32] :
      ( ~ v1_xboole_0(X32)
      | v1_funct_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

fof(c_0_16,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_17,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_18,plain,(
    ! [X18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_19,plain,(
    ! [X48,X49,X50] :
      ( ( v1_funct_1(X50)
        | ~ v1_funct_1(X50)
        | ~ v1_partfun1(X50,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( v1_funct_2(X50,X48,X49)
        | ~ v1_funct_1(X50)
        | ~ v1_partfun1(X50,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_20,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | ~ r1_tarski(X38,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X51,X52,X53] :
      ( ~ v1_xboole_0(X51)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | v1_partfun1(X53,X51) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

fof(c_0_26,plain,(
    ! [X54,X55,X56] :
      ( ( ~ v1_funct_2(X56,X54,X55)
        | X54 = k1_relset_1(X54,X55,X56)
        | X55 = k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( X54 != k1_relset_1(X54,X55,X56)
        | v1_funct_2(X56,X54,X55)
        | X55 = k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( ~ v1_funct_2(X56,X54,X55)
        | X54 = k1_relset_1(X54,X55,X56)
        | X54 != k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( X54 != k1_relset_1(X54,X55,X56)
        | v1_funct_2(X56,X54,X55)
        | X54 != k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( ~ v1_funct_2(X56,X54,X55)
        | X56 = k1_xboole_0
        | X54 = k1_xboole_0
        | X55 != k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( X56 != k1_xboole_0
        | v1_funct_2(X56,X54,X55)
        | X54 = k1_xboole_0
        | X55 != k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_27,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k1_relset_1(X42,X43,X44) = k1_relat_1(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_28,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v1_funct_1(X1)
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( v1_funct_2(X1,X2,X3)
    | r2_hidden(esk1_1(X1),X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( v1_partfun1(X1,X2)
    | r2_hidden(esk1_1(X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

fof(c_0_38,plain,(
    ! [X57,X58,X59,X60,X62,X63,X64,X65,X66,X68] :
      ( ( v1_relat_1(esk6_4(X57,X58,X59,X60))
        | ~ r2_hidden(X60,X59)
        | X59 != k1_funct_2(X57,X58) )
      & ( v1_funct_1(esk6_4(X57,X58,X59,X60))
        | ~ r2_hidden(X60,X59)
        | X59 != k1_funct_2(X57,X58) )
      & ( X60 = esk6_4(X57,X58,X59,X60)
        | ~ r2_hidden(X60,X59)
        | X59 != k1_funct_2(X57,X58) )
      & ( k1_relat_1(esk6_4(X57,X58,X59,X60)) = X57
        | ~ r2_hidden(X60,X59)
        | X59 != k1_funct_2(X57,X58) )
      & ( r1_tarski(k2_relat_1(esk6_4(X57,X58,X59,X60)),X58)
        | ~ r2_hidden(X60,X59)
        | X59 != k1_funct_2(X57,X58) )
      & ( ~ v1_relat_1(X63)
        | ~ v1_funct_1(X63)
        | X62 != X63
        | k1_relat_1(X63) != X57
        | ~ r1_tarski(k2_relat_1(X63),X58)
        | r2_hidden(X62,X59)
        | X59 != k1_funct_2(X57,X58) )
      & ( ~ r2_hidden(esk7_3(X64,X65,X66),X66)
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68)
        | esk7_3(X64,X65,X66) != X68
        | k1_relat_1(X68) != X64
        | ~ r1_tarski(k2_relat_1(X68),X65)
        | X66 = k1_funct_2(X64,X65) )
      & ( v1_relat_1(esk8_3(X64,X65,X66))
        | r2_hidden(esk7_3(X64,X65,X66),X66)
        | X66 = k1_funct_2(X64,X65) )
      & ( v1_funct_1(esk8_3(X64,X65,X66))
        | r2_hidden(esk7_3(X64,X65,X66),X66)
        | X66 = k1_funct_2(X64,X65) )
      & ( esk7_3(X64,X65,X66) = esk8_3(X64,X65,X66)
        | r2_hidden(esk7_3(X64,X65,X66),X66)
        | X66 = k1_funct_2(X64,X65) )
      & ( k1_relat_1(esk8_3(X64,X65,X66)) = X64
        | r2_hidden(esk7_3(X64,X65,X66),X66)
        | X66 = k1_funct_2(X64,X65) )
      & ( r1_tarski(k2_relat_1(esk8_3(X64,X65,X66)),X65)
        | r2_hidden(esk7_3(X64,X65,X66),X66)
        | X66 = k1_funct_2(X64,X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t121_funct_2])).

cnf(c_0_40,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_24])).

cnf(c_0_42,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | ~ v1_partfun1(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_24]),c_0_36])).

cnf(c_0_43,plain,
    ( v1_partfun1(k1_xboole_0,X1)
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_44,plain,
    ( X1 = esk6_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_45,negated_conjecture,
    ( r2_hidden(esk11_0,k1_funct_2(esk9_0,esk10_0))
    & ( ~ v1_funct_1(esk11_0)
      | ~ v1_funct_2(esk11_0,esk9_0,esk10_0)
      | ~ m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_46,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_24]),c_0_41])).

cnf(c_0_47,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( v1_relat_1(esk6_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( esk6_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk11_0,k1_funct_2(esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( k1_relat_1(esk6_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_36])).

fof(c_0_54,plain,(
    ! [X45,X46,X47] :
      ( ~ v1_relat_1(X47)
      | ~ r1_tarski(k1_relat_1(X47),X45)
      | ~ r1_tarski(k2_relat_1(X47),X46)
      | m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_55,plain,
    ( v1_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( esk6_4(esk9_0,esk10_0,k1_funct_2(esk9_0,esk10_0),esk11_0) = esk11_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( k1_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | k1_xboole_0 = X2
    | ~ v1_funct_2(k1_xboole_0,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_24]),c_0_41]),c_0_53])).

cnf(c_0_59,plain,
    ( v1_funct_1(esk6_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_60,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X17,X16)
        | r2_hidden(X17,X16)
        | v1_xboole_0(X16) )
      & ( ~ r2_hidden(X17,X16)
        | m1_subset_1(X17,X16)
        | v1_xboole_0(X16) )
      & ( ~ m1_subset_1(X17,X16)
        | v1_xboole_0(X17)
        | ~ v1_xboole_0(X16) )
      & ( ~ v1_xboole_0(X17)
        | m1_subset_1(X17,X16)
        | ~ v1_xboole_0(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_50]),c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k1_relat_1(esk11_0) = esk9_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_50]),c_0_56])).

cnf(c_0_64,plain,
    ( k1_xboole_0 = X1
    | X2 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_47])).

cnf(c_0_65,plain,
    ( r1_tarski(k2_relat_1(esk6_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_66,plain,
    ( v1_funct_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_68,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(esk11_0),X2)
    | ~ r1_tarski(esk9_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(ef,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( r1_tarski(k2_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(esk6_4(esk9_0,esk10_0,k1_funct_2(esk9_0,esk10_0),esk11_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_50])).

cnf(c_0_73,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_24])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_76,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(esk1_1(esk9_0),esk9_0)
    | ~ r1_tarski(k2_relat_1(esk11_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_31])])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk11_0),esk10_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_50]),c_0_56])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_funct_1(esk11_0)
    | ~ v1_funct_2(esk11_0,esk9_0,esk10_0)
    | ~ m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(rw,[status(thm)],[c_0_72,c_0_56])).

cnf(c_0_82,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_83,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk10_0)))
    | r2_hidden(esk1_1(esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_funct_2(esk11_0,esk9_0,esk10_0)
    | ~ m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_87,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_88,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X2))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,plain,
    ( v1_funct_2(X1,X2,X3)
    | r2_hidden(esk1_1(X2),X2)
    | k1_relset_1(X2,X3,X1) != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_70])).

cnf(c_0_90,negated_conjecture,
    ( k1_relset_1(X1,esk10_0,esk11_0) = esk9_0
    | r2_hidden(esk1_1(esk9_0),esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_85]),c_0_63])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk1_1(esk9_0),esk9_0)
    | ~ v1_funct_2(esk11_0,esk9_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_85])).

cnf(c_0_92,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
    | r2_hidden(esk2_2(X2,X1),X2)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk1_1(esk9_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90])]),c_0_85]),c_0_91])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,X1),esk9_0)
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(esk9_0,esk9_0)
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk9_0))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_96])).

cnf(c_0_98,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_76])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(esk9_0))
    | v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,esk1_1(esk9_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_93])).

cnf(c_0_101,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_83])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(esk9_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,esk2_2(esk9_0,esk1_1(esk9_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_100])).

cnf(c_0_104,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk2_2(X1,esk9_0),X1)
    | r2_hidden(X1,k1_zfmisc_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_107,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(esk9_0,esk9_0)
    | r2_hidden(esk9_0,k1_zfmisc_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_106])).

cnf(c_0_109,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_107,c_0_87])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_108]),c_0_109])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_110])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk11_0),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_111])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_79])).

fof(c_0_114,plain,(
    ! [X39,X40,X41] :
      ( ~ v1_xboole_0(X39)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X40,X39)))
      | v1_xboole_0(X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_115,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_116,negated_conjecture,
    ( k1_relset_1(esk9_0,esk10_0,esk11_0) = esk9_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_113]),c_0_63])).

cnf(c_0_117,negated_conjecture,
    ( ~ v1_funct_2(esk11_0,esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_113])])).

cnf(c_0_118,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_119,negated_conjecture,
    ( esk10_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_113])]),c_0_117])).

cnf(c_0_120,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_41]),c_0_24])])).

cnf(c_0_121,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_21])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_113,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk1_1(esk11_0),esk11_0)
    | ~ v1_funct_2(k1_xboole_0,esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_70]),c_0_24])])).

cnf(c_0_124,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r2_hidden(esk1_1(esk11_0),esk11_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_70]),c_0_53])).

cnf(c_0_125,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_53])])).

cnf(c_0_126,negated_conjecture,
    ( v1_xboole_0(esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_36])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk1_1(esk11_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_125])])).

cnf(c_0_128,negated_conjecture,
    ( ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_126])).

cnf(c_0_129,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_127,c_0_128]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:11:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 6.32/6.55  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 6.32/6.55  # and selection function SelectCQIArEqFirst.
% 6.32/6.55  #
% 6.32/6.55  # Preprocessing time       : 0.030 s
% 6.32/6.55  # Presaturation interreduction done
% 6.32/6.55  
% 6.32/6.55  # Proof found!
% 6.32/6.55  # SZS status Theorem
% 6.32/6.55  # SZS output start CNFRefutation
% 6.32/6.55  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 6.32/6.55  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.32/6.55  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.32/6.55  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.32/6.55  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 6.32/6.55  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.32/6.55  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 6.32/6.55  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.32/6.55  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.32/6.55  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 6.32/6.55  fof(t121_funct_2, conjecture, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 6.32/6.55  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 6.32/6.55  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.32/6.55  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.32/6.55  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 6.32/6.55  fof(c_0_15, plain, ![X32]:(~v1_xboole_0(X32)|v1_funct_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 6.32/6.55  fof(c_0_16, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 6.32/6.55  fof(c_0_17, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 6.32/6.55  fof(c_0_18, plain, ![X18]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 6.32/6.55  fof(c_0_19, plain, ![X48, X49, X50]:((v1_funct_1(X50)|(~v1_funct_1(X50)|~v1_partfun1(X50,X48))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(v1_funct_2(X50,X48,X49)|(~v1_funct_1(X50)|~v1_partfun1(X50,X48))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 6.32/6.55  cnf(c_0_20, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 6.32/6.55  cnf(c_0_21, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 6.32/6.55  fof(c_0_22, plain, ![X37, X38]:(~r2_hidden(X37,X38)|~r1_tarski(X38,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 6.32/6.55  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.32/6.55  cnf(c_0_24, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.32/6.55  fof(c_0_25, plain, ![X51, X52, X53]:(~v1_xboole_0(X51)|(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|v1_partfun1(X53,X51))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 6.32/6.55  fof(c_0_26, plain, ![X54, X55, X56]:((((~v1_funct_2(X56,X54,X55)|X54=k1_relset_1(X54,X55,X56)|X55=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X54!=k1_relset_1(X54,X55,X56)|v1_funct_2(X56,X54,X55)|X55=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))&((~v1_funct_2(X56,X54,X55)|X54=k1_relset_1(X54,X55,X56)|X54!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X54!=k1_relset_1(X54,X55,X56)|v1_funct_2(X56,X54,X55)|X54!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))))&((~v1_funct_2(X56,X54,X55)|X56=k1_xboole_0|X54=k1_xboole_0|X55!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X56!=k1_xboole_0|v1_funct_2(X56,X54,X55)|X54=k1_xboole_0|X55!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 6.32/6.55  fof(c_0_27, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k1_relset_1(X42,X43,X44)=k1_relat_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 6.32/6.55  cnf(c_0_28, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 6.32/6.55  cnf(c_0_29, plain, (v1_funct_1(X1)|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 6.32/6.55  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 6.32/6.55  cnf(c_0_31, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 6.32/6.55  cnf(c_0_32, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 6.32/6.55  cnf(c_0_33, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.32/6.55  cnf(c_0_34, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 6.32/6.55  cnf(c_0_35, plain, (v1_funct_2(X1,X2,X3)|r2_hidden(esk1_1(X1),X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 6.32/6.55  cnf(c_0_36, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 6.32/6.55  cnf(c_0_37, plain, (v1_partfun1(X1,X2)|r2_hidden(esk1_1(X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 6.32/6.55  fof(c_0_38, plain, ![X57, X58, X59, X60, X62, X63, X64, X65, X66, X68]:(((((((v1_relat_1(esk6_4(X57,X58,X59,X60))|~r2_hidden(X60,X59)|X59!=k1_funct_2(X57,X58))&(v1_funct_1(esk6_4(X57,X58,X59,X60))|~r2_hidden(X60,X59)|X59!=k1_funct_2(X57,X58)))&(X60=esk6_4(X57,X58,X59,X60)|~r2_hidden(X60,X59)|X59!=k1_funct_2(X57,X58)))&(k1_relat_1(esk6_4(X57,X58,X59,X60))=X57|~r2_hidden(X60,X59)|X59!=k1_funct_2(X57,X58)))&(r1_tarski(k2_relat_1(esk6_4(X57,X58,X59,X60)),X58)|~r2_hidden(X60,X59)|X59!=k1_funct_2(X57,X58)))&(~v1_relat_1(X63)|~v1_funct_1(X63)|X62!=X63|k1_relat_1(X63)!=X57|~r1_tarski(k2_relat_1(X63),X58)|r2_hidden(X62,X59)|X59!=k1_funct_2(X57,X58)))&((~r2_hidden(esk7_3(X64,X65,X66),X66)|(~v1_relat_1(X68)|~v1_funct_1(X68)|esk7_3(X64,X65,X66)!=X68|k1_relat_1(X68)!=X64|~r1_tarski(k2_relat_1(X68),X65))|X66=k1_funct_2(X64,X65))&(((((v1_relat_1(esk8_3(X64,X65,X66))|r2_hidden(esk7_3(X64,X65,X66),X66)|X66=k1_funct_2(X64,X65))&(v1_funct_1(esk8_3(X64,X65,X66))|r2_hidden(esk7_3(X64,X65,X66),X66)|X66=k1_funct_2(X64,X65)))&(esk7_3(X64,X65,X66)=esk8_3(X64,X65,X66)|r2_hidden(esk7_3(X64,X65,X66),X66)|X66=k1_funct_2(X64,X65)))&(k1_relat_1(esk8_3(X64,X65,X66))=X64|r2_hidden(esk7_3(X64,X65,X66),X66)|X66=k1_funct_2(X64,X65)))&(r1_tarski(k2_relat_1(esk8_3(X64,X65,X66)),X65)|r2_hidden(esk7_3(X64,X65,X66),X66)|X66=k1_funct_2(X64,X65))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 6.32/6.55  fof(c_0_39, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t121_funct_2])).
% 6.32/6.55  cnf(c_0_40, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_33])).
% 6.32/6.55  cnf(c_0_41, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_24])).
% 6.32/6.55  cnf(c_0_42, plain, (v1_funct_2(k1_xboole_0,X1,X2)|~v1_partfun1(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_24]), c_0_36])).
% 6.32/6.55  cnf(c_0_43, plain, (v1_partfun1(k1_xboole_0,X1)|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_37, c_0_24])).
% 6.32/6.55  cnf(c_0_44, plain, (X1=esk6_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 6.32/6.55  fof(c_0_45, negated_conjecture, (r2_hidden(esk11_0,k1_funct_2(esk9_0,esk10_0))&(~v1_funct_1(esk11_0)|~v1_funct_2(esk11_0,esk9_0,esk10_0)|~m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 6.32/6.55  cnf(c_0_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_24]), c_0_41])).
% 6.32/6.55  cnf(c_0_47, plain, (v1_funct_2(k1_xboole_0,X1,X2)|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 6.32/6.55  cnf(c_0_48, plain, (v1_relat_1(esk6_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 6.32/6.55  cnf(c_0_49, plain, (esk6_4(X1,X2,k1_funct_2(X1,X2),X3)=X3|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_44])).
% 6.32/6.55  cnf(c_0_50, negated_conjecture, (r2_hidden(esk11_0,k1_funct_2(esk9_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 6.32/6.55  cnf(c_0_51, plain, (k1_relat_1(esk6_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 6.32/6.55  cnf(c_0_52, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.32/6.55  cnf(c_0_53, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_36])).
% 6.32/6.55  fof(c_0_54, plain, ![X45, X46, X47]:(~v1_relat_1(X47)|(~r1_tarski(k1_relat_1(X47),X45)|~r1_tarski(k2_relat_1(X47),X46)|m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 6.32/6.55  cnf(c_0_55, plain, (v1_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_48])).
% 6.32/6.55  cnf(c_0_56, negated_conjecture, (esk6_4(esk9_0,esk10_0,k1_funct_2(esk9_0,esk10_0),esk11_0)=esk11_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 6.32/6.55  cnf(c_0_57, plain, (k1_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))=X1|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_51])).
% 6.32/6.55  cnf(c_0_58, plain, (X1=k1_xboole_0|k1_xboole_0=X2|~v1_funct_2(k1_xboole_0,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_24]), c_0_41]), c_0_53])).
% 6.32/6.55  cnf(c_0_59, plain, (v1_funct_1(esk6_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 6.32/6.55  fof(c_0_60, plain, ![X16, X17]:(((~m1_subset_1(X17,X16)|r2_hidden(X17,X16)|v1_xboole_0(X16))&(~r2_hidden(X17,X16)|m1_subset_1(X17,X16)|v1_xboole_0(X16)))&((~m1_subset_1(X17,X16)|v1_xboole_0(X17)|~v1_xboole_0(X16))&(~v1_xboole_0(X17)|m1_subset_1(X17,X16)|~v1_xboole_0(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 6.32/6.55  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 6.32/6.55  cnf(c_0_62, negated_conjecture, (v1_relat_1(esk11_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_50]), c_0_56])).
% 6.32/6.55  cnf(c_0_63, negated_conjecture, (k1_relat_1(esk11_0)=esk9_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_50]), c_0_56])).
% 6.32/6.55  cnf(c_0_64, plain, (k1_xboole_0=X1|X2=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_58, c_0_47])).
% 6.32/6.55  cnf(c_0_65, plain, (r1_tarski(k2_relat_1(esk6_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 6.32/6.55  cnf(c_0_66, plain, (v1_funct_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3))|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_59])).
% 6.32/6.55  cnf(c_0_67, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 6.32/6.55  fof(c_0_68, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 6.32/6.55  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k2_relat_1(esk11_0),X2)|~r1_tarski(esk9_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 6.32/6.55  cnf(c_0_70, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(ef,[status(thm)],[c_0_64])).
% 6.32/6.55  cnf(c_0_71, plain, (r1_tarski(k2_relat_1(esk6_4(X1,X2,k1_funct_2(X1,X2),X3)),X2)|~r2_hidden(X3,k1_funct_2(X1,X2))), inference(er,[status(thm)],[c_0_65])).
% 6.32/6.55  cnf(c_0_72, negated_conjecture, (v1_funct_1(esk6_4(esk9_0,esk10_0,k1_funct_2(esk9_0,esk10_0),esk11_0))), inference(spm,[status(thm)],[c_0_66, c_0_50])).
% 6.32/6.55  cnf(c_0_73, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 6.32/6.55  cnf(c_0_74, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))|v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_67, c_0_24])).
% 6.32/6.55  cnf(c_0_75, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.32/6.55  cnf(c_0_76, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 6.32/6.55  cnf(c_0_77, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.32/6.55  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|r2_hidden(esk1_1(esk9_0),esk9_0)|~r1_tarski(k2_relat_1(esk11_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_31])])).
% 6.32/6.55  cnf(c_0_79, negated_conjecture, (r1_tarski(k2_relat_1(esk11_0),esk10_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_50]), c_0_56])).
% 6.32/6.55  cnf(c_0_80, negated_conjecture, (~v1_funct_1(esk11_0)|~v1_funct_2(esk11_0,esk9_0,esk10_0)|~m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 6.32/6.55  cnf(c_0_81, negated_conjecture, (v1_funct_1(esk11_0)), inference(rw,[status(thm)],[c_0_72, c_0_56])).
% 6.32/6.55  cnf(c_0_82, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))|v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 6.32/6.55  cnf(c_0_83, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 6.32/6.55  cnf(c_0_84, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_77])).
% 6.32/6.55  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk10_0)))|r2_hidden(esk1_1(esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 6.32/6.55  cnf(c_0_86, negated_conjecture, (~v1_funct_2(esk11_0,esk9_0,esk10_0)|~m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 6.32/6.55  cnf(c_0_87, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 6.32/6.55  cnf(c_0_88, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(k1_xboole_0,k1_zfmisc_1(X2))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 6.32/6.55  cnf(c_0_89, plain, (v1_funct_2(X1,X2,X3)|r2_hidden(esk1_1(X2),X2)|k1_relset_1(X2,X3,X1)!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_84, c_0_70])).
% 6.32/6.55  cnf(c_0_90, negated_conjecture, (k1_relset_1(X1,esk10_0,esk11_0)=esk9_0|r2_hidden(esk1_1(esk9_0),esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_85]), c_0_63])).
% 6.32/6.55  cnf(c_0_91, negated_conjecture, (r2_hidden(esk1_1(esk9_0),esk9_0)|~v1_funct_2(esk11_0,esk9_0,esk10_0)), inference(spm,[status(thm)],[c_0_86, c_0_85])).
% 6.32/6.55  cnf(c_0_92, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))|r2_hidden(esk2_2(X2,X1),X2)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 6.32/6.55  cnf(c_0_93, negated_conjecture, (r2_hidden(esk1_1(esk9_0),esk9_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90])]), c_0_85]), c_0_91])).
% 6.32/6.55  cnf(c_0_94, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 6.32/6.55  cnf(c_0_95, negated_conjecture, (r2_hidden(esk2_2(esk9_0,X1),esk9_0)|r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 6.32/6.55  cnf(c_0_96, negated_conjecture, (r1_tarski(esk9_0,esk9_0)|r2_hidden(k1_xboole_0,k1_zfmisc_1(esk9_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 6.32/6.55  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(esk9_0))|r2_hidden(k1_xboole_0,k1_zfmisc_1(esk9_0))), inference(spm,[status(thm)],[c_0_75, c_0_96])).
% 6.32/6.55  cnf(c_0_98, plain, (r2_hidden(esk2_2(X1,X2),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_30, c_0_76])).
% 6.32/6.55  cnf(c_0_99, negated_conjecture, (r2_hidden(k1_xboole_0,k1_zfmisc_1(esk9_0))|v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_82, c_0_97])).
% 6.32/6.55  cnf(c_0_100, negated_conjecture, (r2_hidden(esk2_2(esk9_0,esk1_1(esk9_0)),esk9_0)), inference(spm,[status(thm)],[c_0_98, c_0_93])).
% 6.32/6.55  cnf(c_0_101, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(X1,k1_zfmisc_1(X2))|v1_xboole_0(k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_67, c_0_83])).
% 6.32/6.55  cnf(c_0_102, negated_conjecture, (r2_hidden(k1_xboole_0,k1_zfmisc_1(esk9_0))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_87, c_0_99])).
% 6.32/6.55  cnf(c_0_103, negated_conjecture, (r2_hidden(esk2_2(esk9_0,esk2_2(esk9_0,esk1_1(esk9_0))),esk9_0)), inference(spm,[status(thm)],[c_0_98, c_0_100])).
% 6.32/6.55  cnf(c_0_104, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_87, c_0_101])).
% 6.32/6.55  cnf(c_0_105, negated_conjecture, (r2_hidden(k1_xboole_0,k1_zfmisc_1(esk9_0))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 6.32/6.55  cnf(c_0_106, negated_conjecture, (r2_hidden(esk2_2(X1,esk9_0),X1)|r2_hidden(X1,k1_zfmisc_1(esk9_0))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 6.32/6.55  cnf(c_0_107, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 6.32/6.55  cnf(c_0_108, negated_conjecture, (r1_tarski(esk9_0,esk9_0)|r2_hidden(esk9_0,k1_zfmisc_1(esk9_0))), inference(spm,[status(thm)],[c_0_94, c_0_106])).
% 6.32/6.55  cnf(c_0_109, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_107, c_0_87])).
% 6.32/6.55  cnf(c_0_110, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_108]), c_0_109])).
% 6.32/6.55  cnf(c_0_111, negated_conjecture, (r1_tarski(esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_23, c_0_110])).
% 6.32/6.55  cnf(c_0_112, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,X1)))|~r1_tarski(k2_relat_1(esk11_0),X1)), inference(spm,[status(thm)],[c_0_69, c_0_111])).
% 6.32/6.55  cnf(c_0_113, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_112, c_0_79])).
% 6.32/6.55  fof(c_0_114, plain, ![X39, X40, X41]:(~v1_xboole_0(X39)|(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X40,X39)))|v1_xboole_0(X41))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 6.32/6.55  cnf(c_0_115, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.32/6.55  cnf(c_0_116, negated_conjecture, (k1_relset_1(esk9_0,esk10_0,esk11_0)=esk9_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_113]), c_0_63])).
% 6.32/6.55  cnf(c_0_117, negated_conjecture, (~v1_funct_2(esk11_0,esk9_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_113])])).
% 6.32/6.55  cnf(c_0_118, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_114])).
% 6.32/6.55  cnf(c_0_119, negated_conjecture, (esk10_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_113])]), c_0_117])).
% 6.32/6.55  cnf(c_0_120, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_41]), c_0_24])])).
% 6.32/6.55  cnf(c_0_121, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(spm,[status(thm)],[c_0_118, c_0_21])).
% 6.32/6.55  cnf(c_0_122, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_113, c_0_119])).
% 6.32/6.55  cnf(c_0_123, negated_conjecture, (r2_hidden(esk1_1(esk11_0),esk11_0)|~v1_funct_2(k1_xboole_0,esk9_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_70]), c_0_24])])).
% 6.32/6.55  cnf(c_0_124, negated_conjecture, (esk9_0=k1_xboole_0|r2_hidden(esk1_1(esk11_0),esk11_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_70]), c_0_53])).
% 6.32/6.55  cnf(c_0_125, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_53])])).
% 6.32/6.55  cnf(c_0_126, negated_conjecture, (v1_xboole_0(esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_36])).
% 6.32/6.55  cnf(c_0_127, negated_conjecture, (r2_hidden(esk1_1(esk11_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_125])])).
% 6.32/6.55  cnf(c_0_128, negated_conjecture, (~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_87, c_0_126])).
% 6.32/6.55  cnf(c_0_129, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_127, c_0_128]), ['proof']).
% 6.32/6.55  # SZS output end CNFRefutation
% 6.32/6.55  # Proof object total steps             : 130
% 6.32/6.55  # Proof object clause steps            : 99
% 6.32/6.55  # Proof object formula steps           : 31
% 6.32/6.55  # Proof object conjectures             : 42
% 6.32/6.55  # Proof object clause conjectures      : 39
% 6.32/6.55  # Proof object formula conjectures     : 3
% 6.32/6.55  # Proof object initial clauses used    : 28
% 6.32/6.55  # Proof object initial formulas used   : 15
% 6.32/6.55  # Proof object generating inferences   : 57
% 6.32/6.55  # Proof object simplifying inferences  : 45
% 6.32/6.55  # Training examples: 0 positive, 0 negative
% 6.32/6.55  # Parsed axioms                        : 19
% 6.32/6.55  # Removed by relevancy pruning/SinE    : 0
% 6.32/6.55  # Initial clauses                      : 49
% 6.32/6.55  # Removed in clause preprocessing      : 1
% 6.32/6.55  # Initial clauses in saturation        : 48
% 6.32/6.55  # Processed clauses                    : 14682
% 6.32/6.55  # ...of these trivial                  : 375
% 6.32/6.55  # ...subsumed                          : 9884
% 6.32/6.55  # ...remaining for further processing  : 4423
% 6.32/6.55  # Other redundant clauses eliminated   : 1618
% 6.32/6.55  # Clauses deleted for lack of memory   : 0
% 6.32/6.55  # Backward-subsumed                    : 470
% 6.32/6.55  # Backward-rewritten                   : 2915
% 6.32/6.55  # Generated clauses                    : 982030
% 6.32/6.55  # ...of the previous two non-trivial   : 890087
% 6.32/6.55  # Contextual simplify-reflections      : 83
% 6.32/6.55  # Paramodulations                      : 980309
% 6.32/6.55  # Factorizations                       : 76
% 6.32/6.55  # Equation resolutions                 : 1618
% 6.32/6.55  # Propositional unsat checks           : 0
% 6.32/6.55  #    Propositional check models        : 0
% 6.32/6.55  #    Propositional check unsatisfiable : 0
% 6.32/6.55  #    Propositional clauses             : 0
% 6.32/6.55  #    Propositional clauses after purity: 0
% 6.32/6.55  #    Propositional unsat core size     : 0
% 6.32/6.55  #    Propositional preprocessing time  : 0.000
% 6.32/6.55  #    Propositional encoding time       : 0.000
% 6.32/6.55  #    Propositional solver time         : 0.000
% 6.32/6.55  #    Success case prop preproc time    : 0.000
% 6.32/6.55  #    Success case prop encoding time   : 0.000
% 6.32/6.55  #    Success case prop solver time     : 0.000
% 6.32/6.55  # Current number of processed clauses  : 947
% 6.32/6.55  #    Positive orientable unit clauses  : 86
% 6.32/6.55  #    Positive unorientable unit clauses: 0
% 6.32/6.55  #    Negative unit clauses             : 21
% 6.32/6.55  #    Non-unit-clauses                  : 840
% 6.32/6.55  # Current number of unprocessed clauses: 869570
% 6.32/6.55  # ...number of literals in the above   : 4520753
% 6.32/6.55  # Current number of archived formulas  : 0
% 6.32/6.55  # Current number of archived clauses   : 3462
% 6.32/6.55  # Clause-clause subsumption calls (NU) : 4911378
% 6.32/6.55  # Rec. Clause-clause subsumption calls : 1606961
% 6.32/6.55  # Non-unit clause-clause subsumptions  : 9782
% 6.32/6.55  # Unit Clause-clause subsumption calls : 99653
% 6.32/6.55  # Rewrite failures with RHS unbound    : 0
% 6.32/6.55  # BW rewrite match attempts            : 156
% 6.32/6.55  # BW rewrite match successes           : 36
% 6.32/6.55  # Condensation attempts                : 0
% 6.32/6.55  # Condensation successes               : 0
% 6.32/6.55  # Termbank termtop insertions          : 18664437
% 6.32/6.58  
% 6.32/6.58  # -------------------------------------------------
% 6.32/6.58  # User time                : 5.930 s
% 6.32/6.58  # System time              : 0.300 s
% 6.32/6.58  # Total time               : 6.230 s
% 6.32/6.58  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
