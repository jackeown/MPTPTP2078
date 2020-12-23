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
% DateTime   : Thu Dec  3 11:05:13 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 242 expanded)
%              Number of clauses        :   41 (  93 expanded)
%              Number of leaves         :   19 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  313 ( 574 expanded)
%              Number of equality atoms :  145 ( 295 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

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

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk10_0)
    & v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0))
    & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0))))
    & r2_hidden(esk9_0,esk7_0)
    & k1_funct_1(esk10_0,esk9_0) != esk8_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_21,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X31,X32,X33,X34] : k3_enumset1(X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X35,X36,X37,X38,X39] : k4_enumset1(X35,X35,X36,X37,X38,X39) = k3_enumset1(X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X40,X41,X42,X43,X44,X45] : k5_enumset1(X40,X40,X41,X42,X43,X44,X45) = k4_enumset1(X40,X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52] : k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52) = k5_enumset1(X46,X47,X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_28,plain,(
    ! [X94,X95,X96] :
      ( ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,X95)))
      | k1_relset_1(X94,X95,X96) = k1_relat_1(X96) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X76,X77,X78,X80,X81,X82,X84] :
      ( ( r2_hidden(esk4_3(X76,X77,X78),k1_relat_1(X76))
        | ~ r2_hidden(X78,X77)
        | X77 != k2_relat_1(X76)
        | ~ v1_relat_1(X76)
        | ~ v1_funct_1(X76) )
      & ( X78 = k1_funct_1(X76,esk4_3(X76,X77,X78))
        | ~ r2_hidden(X78,X77)
        | X77 != k2_relat_1(X76)
        | ~ v1_relat_1(X76)
        | ~ v1_funct_1(X76) )
      & ( ~ r2_hidden(X81,k1_relat_1(X76))
        | X80 != k1_funct_1(X76,X81)
        | r2_hidden(X80,X77)
        | X77 != k2_relat_1(X76)
        | ~ v1_relat_1(X76)
        | ~ v1_funct_1(X76) )
      & ( ~ r2_hidden(esk5_2(X76,X82),X82)
        | ~ r2_hidden(X84,k1_relat_1(X76))
        | esk5_2(X76,X82) != k1_funct_1(X76,X84)
        | X82 = k2_relat_1(X76)
        | ~ v1_relat_1(X76)
        | ~ v1_funct_1(X76) )
      & ( r2_hidden(esk6_2(X76,X82),k1_relat_1(X76))
        | r2_hidden(esk5_2(X76,X82),X82)
        | X82 = k2_relat_1(X76)
        | ~ v1_relat_1(X76)
        | ~ v1_funct_1(X76) )
      & ( esk5_2(X76,X82) = k1_funct_1(X76,esk6_2(X76,X82))
        | r2_hidden(esk5_2(X76,X82),X82)
        | X82 = k2_relat_1(X76)
        | ~ v1_relat_1(X76)
        | ~ v1_funct_1(X76) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_38,plain,(
    ! [X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67,X68,X69,X70,X71,X72] :
      ( ( ~ r2_hidden(X62,X61)
        | X62 = X53
        | X62 = X54
        | X62 = X55
        | X62 = X56
        | X62 = X57
        | X62 = X58
        | X62 = X59
        | X62 = X60
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X53
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X54
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X55
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X56
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X57
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X58
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X59
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X60
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X64
        | ~ r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X65
        | ~ r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X66
        | ~ r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X67
        | ~ r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X68
        | ~ r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X69
        | ~ r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X70
        | ~ r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X71
        | ~ r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X64
        | esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X65
        | esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X66
        | esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X67
        | esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X68
        | esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X69
        | esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X70
        | esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X71
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

fof(c_0_39,plain,(
    ! [X97,X98,X99] :
      ( ( ~ v1_funct_2(X99,X97,X98)
        | X97 = k1_relset_1(X97,X98,X99)
        | X98 = k1_xboole_0
        | ~ m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98))) )
      & ( X97 != k1_relset_1(X97,X98,X99)
        | v1_funct_2(X99,X97,X98)
        | X98 = k1_xboole_0
        | ~ m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98))) )
      & ( ~ v1_funct_2(X99,X97,X98)
        | X97 = k1_relset_1(X97,X98,X99)
        | X97 != k1_xboole_0
        | ~ m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98))) )
      & ( X97 != k1_relset_1(X97,X98,X99)
        | v1_funct_2(X99,X97,X98)
        | X97 != k1_xboole_0
        | ~ m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98))) )
      & ( ~ v1_funct_2(X99,X97,X98)
        | X99 = k1_xboole_0
        | X97 = k1_xboole_0
        | X98 != k1_xboole_0
        | ~ m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98))) )
      & ( X99 != k1_xboole_0
        | v1_funct_2(X99,X97,X98)
        | X97 = k1_xboole_0
        | X98 != k1_xboole_0
        | ~ m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_40,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_43,plain,(
    ! [X86,X87] :
      ( ~ r2_hidden(X86,X87)
      | ~ r1_tarski(X87,X86) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_44,plain,(
    ! [X17] : r1_tarski(k1_xboole_0,X17) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_45,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk1_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk1_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_46,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( k1_relset_1(esk7_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),esk10_0) = k1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk10_0,esk7_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_53,plain,(
    ! [X88,X89,X90] :
      ( ~ m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X88,X89)))
      | v1_relat_1(X90) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_54,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).

cnf(c_0_57,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | k1_relat_1(esk10_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_41]),c_0_49]),c_0_50])])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_60,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X18
        | X19 != k1_tarski(X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k1_tarski(X18) )
      & ( ~ r2_hidden(esk2_2(X22,X23),X23)
        | esk2_2(X22,X23) != X22
        | X23 = k1_tarski(X22) )
      & ( r2_hidden(esk2_2(X22,X23),X23)
        | esk2_2(X22,X23) = X22
        | X23 = k1_tarski(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_61,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( k1_relat_1(esk10_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_41])).

fof(c_0_65,plain,(
    ! [X74,X75] :
      ( ( ~ v5_relat_1(X75,X74)
        | r1_tarski(k2_relat_1(X75),X74)
        | ~ v1_relat_1(X75) )
      & ( ~ r1_tarski(k2_relat_1(X75),X74)
        | v5_relat_1(X75,X74)
        | ~ v1_relat_1(X75) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_66,plain,(
    ! [X91,X92,X93] :
      ( ( v4_relat_1(X93,X91)
        | ~ m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(X91,X92))) )
      & ( v5_relat_1(X93,X92)
        | ~ m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(X91,X92))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_67,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk10_0,X1),X2)
    | ~ r2_hidden(X1,esk7_0)
    | ~ r1_tarski(k2_relat_1(esk10_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_69,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk10_0,X1),X2)
    | ~ v5_relat_1(esk10_0,X2)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_64])])).

cnf(c_0_73,negated_conjecture,
    ( v5_relat_1(esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_41])).

cnf(c_0_74,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk10_0,X1),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( k1_funct_1(esk10_0,esk9_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_77,negated_conjecture,
    ( k1_funct_1(esk10_0,X1) = esk8_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk9_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:32:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.029 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 0.12/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.12/0.37  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.12/0.37  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.12/0.37  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 0.12/0.37  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.12/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.12/0.37  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.12/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.12/0.37  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.12/0.37  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0)))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0)))))&(r2_hidden(esk9_0,esk7_0)&k1_funct_1(esk10_0,esk9_0)!=esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.12/0.37  fof(c_0_21, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.37  fof(c_0_22, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  fof(c_0_23, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.37  fof(c_0_24, plain, ![X31, X32, X33, X34]:k3_enumset1(X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.37  fof(c_0_25, plain, ![X35, X36, X37, X38, X39]:k4_enumset1(X35,X35,X36,X37,X38,X39)=k3_enumset1(X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.37  fof(c_0_26, plain, ![X40, X41, X42, X43, X44, X45]:k5_enumset1(X40,X40,X41,X42,X43,X44,X45)=k4_enumset1(X40,X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.37  fof(c_0_27, plain, ![X46, X47, X48, X49, X50, X51, X52]:k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52)=k5_enumset1(X46,X47,X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.12/0.37  fof(c_0_28, plain, ![X94, X95, X96]:(~m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,X95)))|k1_relset_1(X94,X95,X96)=k1_relat_1(X96)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_34, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_35, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_36, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  fof(c_0_37, plain, ![X76, X77, X78, X80, X81, X82, X84]:((((r2_hidden(esk4_3(X76,X77,X78),k1_relat_1(X76))|~r2_hidden(X78,X77)|X77!=k2_relat_1(X76)|(~v1_relat_1(X76)|~v1_funct_1(X76)))&(X78=k1_funct_1(X76,esk4_3(X76,X77,X78))|~r2_hidden(X78,X77)|X77!=k2_relat_1(X76)|(~v1_relat_1(X76)|~v1_funct_1(X76))))&(~r2_hidden(X81,k1_relat_1(X76))|X80!=k1_funct_1(X76,X81)|r2_hidden(X80,X77)|X77!=k2_relat_1(X76)|(~v1_relat_1(X76)|~v1_funct_1(X76))))&((~r2_hidden(esk5_2(X76,X82),X82)|(~r2_hidden(X84,k1_relat_1(X76))|esk5_2(X76,X82)!=k1_funct_1(X76,X84))|X82=k2_relat_1(X76)|(~v1_relat_1(X76)|~v1_funct_1(X76)))&((r2_hidden(esk6_2(X76,X82),k1_relat_1(X76))|r2_hidden(esk5_2(X76,X82),X82)|X82=k2_relat_1(X76)|(~v1_relat_1(X76)|~v1_funct_1(X76)))&(esk5_2(X76,X82)=k1_funct_1(X76,esk6_2(X76,X82))|r2_hidden(esk5_2(X76,X82),X82)|X82=k2_relat_1(X76)|(~v1_relat_1(X76)|~v1_funct_1(X76)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.12/0.37  fof(c_0_38, plain, ![X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67, X68, X69, X70, X71, X72]:(((~r2_hidden(X62,X61)|(X62=X53|X62=X54|X62=X55|X62=X56|X62=X57|X62=X58|X62=X59|X62=X60)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60))&((((((((X63!=X53|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60))&(X63!=X54|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60)))&(X63!=X55|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60)))&(X63!=X56|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60)))&(X63!=X57|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60)))&(X63!=X58|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60)))&(X63!=X59|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60)))&(X63!=X60|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60))))&(((((((((esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X64|~r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71))&(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X65|~r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X66|~r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X67|~r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X68|~r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X69|~r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X70|~r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X71|~r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(r2_hidden(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|(esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X64|esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X65|esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X66|esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X67|esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X68|esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X69|esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X70|esk3_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X71)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.12/0.37  fof(c_0_39, plain, ![X97, X98, X99]:((((~v1_funct_2(X99,X97,X98)|X97=k1_relset_1(X97,X98,X99)|X98=k1_xboole_0|~m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98))))&(X97!=k1_relset_1(X97,X98,X99)|v1_funct_2(X99,X97,X98)|X98=k1_xboole_0|~m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98)))))&((~v1_funct_2(X99,X97,X98)|X97=k1_relset_1(X97,X98,X99)|X97!=k1_xboole_0|~m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98))))&(X97!=k1_relset_1(X97,X98,X99)|v1_funct_2(X99,X97,X98)|X97!=k1_xboole_0|~m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98))))))&((~v1_funct_2(X99,X97,X98)|X99=k1_xboole_0|X97=k1_xboole_0|X98!=k1_xboole_0|~m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98))))&(X99!=k1_xboole_0|v1_funct_2(X99,X97,X98)|X97=k1_xboole_0|X98!=k1_xboole_0|~m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.12/0.37  cnf(c_0_40, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  fof(c_0_43, plain, ![X86, X87]:(~r2_hidden(X86,X87)|~r1_tarski(X87,X86)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.37  fof(c_0_44, plain, ![X17]:r1_tarski(k1_xboole_0,X17), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.37  fof(c_0_45, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk1_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk1_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  cnf(c_0_46, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.37  cnf(c_0_48, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (k1_relset_1(esk7_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),esk10_0)=k1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk10_0,esk7_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.12/0.37  cnf(c_0_51, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.37  cnf(c_0_52, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.37  fof(c_0_53, plain, ![X88, X89, X90]:(~m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X88,X89)))|v1_relat_1(X90)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.37  cnf(c_0_54, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.37  cnf(c_0_55, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 0.12/0.37  cnf(c_0_56, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)=k1_xboole_0|k1_relat_1(esk10_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_41]), c_0_49]), c_0_50])])).
% 0.12/0.37  cnf(c_0_58, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.37  cnf(c_0_59, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.12/0.37  fof(c_0_60, plain, ![X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X20,X19)|X20=X18|X19!=k1_tarski(X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k1_tarski(X18)))&((~r2_hidden(esk2_2(X22,X23),X23)|esk2_2(X22,X23)!=X22|X23=k1_tarski(X22))&(r2_hidden(esk2_2(X22,X23),X23)|esk2_2(X22,X23)=X22|X23=k1_tarski(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.12/0.37  cnf(c_0_61, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (k1_relat_1(esk10_0)=esk7_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.12/0.37  cnf(c_0_63, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (v1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_59, c_0_41])).
% 0.12/0.37  fof(c_0_65, plain, ![X74, X75]:((~v5_relat_1(X75,X74)|r1_tarski(k2_relat_1(X75),X74)|~v1_relat_1(X75))&(~r1_tarski(k2_relat_1(X75),X74)|v5_relat_1(X75,X74)|~v1_relat_1(X75))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.12/0.37  fof(c_0_66, plain, ![X91, X92, X93]:((v4_relat_1(X93,X91)|~m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(X91,X92))))&(v5_relat_1(X93,X92)|~m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(X91,X92))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.12/0.37  cnf(c_0_67, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.12/0.37  cnf(c_0_68, negated_conjecture, (r2_hidden(k1_funct_1(esk10_0,X1),X2)|~r2_hidden(X1,esk7_0)|~r1_tarski(k2_relat_1(esk10_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])])).
% 0.12/0.37  cnf(c_0_69, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.12/0.37  cnf(c_0_70, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.12/0.37  cnf(c_0_71, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.12/0.37  cnf(c_0_72, negated_conjecture, (r2_hidden(k1_funct_1(esk10_0,X1),X2)|~v5_relat_1(esk10_0,X2)|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_64])])).
% 0.12/0.37  cnf(c_0_73, negated_conjecture, (v5_relat_1(esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_70, c_0_41])).
% 0.12/0.37  cnf(c_0_74, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_71])).
% 0.12/0.37  cnf(c_0_75, negated_conjecture, (r2_hidden(k1_funct_1(esk10_0,X1),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.12/0.37  cnf(c_0_76, negated_conjecture, (k1_funct_1(esk10_0,esk9_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_77, negated_conjecture, (k1_funct_1(esk10_0,X1)=esk8_0|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.12/0.37  cnf(c_0_78, negated_conjecture, (r2_hidden(esk9_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_79, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 80
% 0.12/0.37  # Proof object clause steps            : 41
% 0.12/0.37  # Proof object formula steps           : 39
% 0.12/0.37  # Proof object conjectures             : 20
% 0.12/0.37  # Proof object clause conjectures      : 17
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 23
% 0.12/0.37  # Proof object initial formulas used   : 19
% 0.12/0.37  # Proof object generating inferences   : 12
% 0.12/0.37  # Proof object simplifying inferences  : 37
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 19
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 57
% 0.12/0.37  # Removed in clause preprocessing      : 7
% 0.12/0.37  # Initial clauses in saturation        : 50
% 0.12/0.37  # Processed clauses                    : 123
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 4
% 0.12/0.37  # ...remaining for further processing  : 119
% 0.12/0.37  # Other redundant clauses eliminated   : 29
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 2
% 0.12/0.37  # Generated clauses                    : 73
% 0.12/0.37  # ...of the previous two non-trivial   : 65
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 55
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 29
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 50
% 0.12/0.37  #    Positive orientable unit clauses  : 18
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 4
% 0.12/0.37  #    Non-unit-clauses                  : 28
% 0.12/0.37  # Current number of unprocessed clauses: 29
% 0.12/0.37  # ...number of literals in the above   : 102
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 58
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 474
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 249
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.12/0.37  # Unit Clause-clause subsumption calls : 24
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 69
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4640
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.033 s
% 0.12/0.37  # System time              : 0.006 s
% 0.12/0.37  # Total time               : 0.039 s
% 0.12/0.37  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
