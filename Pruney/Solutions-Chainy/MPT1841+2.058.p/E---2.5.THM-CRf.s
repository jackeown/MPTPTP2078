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
% DateTime   : Thu Dec  3 11:19:01 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 114 expanded)
%              Number of clauses        :   38 (  48 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  241 ( 349 expanded)
%              Number of equality atoms :   95 (  95 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(t6_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(cc2_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_xboole_0(X2)
           => ~ v1_subset_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(cc4_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ~ v1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_20,plain,(
    ! [X80,X81,X82] :
      ( ~ r2_hidden(X80,X81)
      | ~ m1_subset_1(X81,k1_zfmisc_1(X82))
      | ~ v1_xboole_0(X82) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_21,plain,(
    ! [X74] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X74)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( ~ r1_tarski(X15,X16)
        | ~ r2_hidden(X17,X15)
        | r2_hidden(X17,X16) )
      & ( r2_hidden(esk2_2(X18,X19),X18)
        | r1_tarski(X18,X19) )
      & ( ~ r2_hidden(esk2_2(X18,X19),X19)
        | r1_tarski(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_27,plain,(
    ! [X72] :
      ( m1_subset_1(esk4_1(X72),k1_zfmisc_1(X72))
      & v1_xboole_0(esk4_1(X72)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
                & v1_zfmisc_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tex_2])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(X21,X22)
        | X21 != X22 )
      & ( r1_tarski(X22,X21)
        | X21 != X22 )
      & ( ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X21)
        | X21 = X22 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( v1_xboole_0(esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v1_xboole_0(X11)
        | ~ r2_hidden(X12,X11) )
      & ( r2_hidden(esk1_1(X13),X13)
        | v1_xboole_0(X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_33,plain,(
    ! [X89,X90] :
      ( v1_xboole_0(X89)
      | ~ v1_zfmisc_1(X89)
      | ~ m1_subset_1(X90,k1_zfmisc_1(X89))
      | v1_xboole_0(X90)
      | ~ v1_subset_1(X90,X89) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).

fof(c_0_34,plain,(
    ! [X75,X76] :
      ( ~ v1_xboole_0(X75)
      | ~ m1_subset_1(X76,k1_zfmisc_1(X75))
      | ~ v1_subset_1(X76,X75) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).

fof(c_0_35,plain,(
    ! [X85,X86] :
      ( v1_xboole_0(X85)
      | ~ m1_subset_1(X86,X85)
      | m1_subset_1(k6_domain_1(X85,X86),k1_zfmisc_1(X85)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0)
    & m1_subset_1(esk6_0,esk5_0)
    & v1_subset_1(k6_domain_1(esk5_0,esk6_0),esk5_0)
    & v1_zfmisc_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X87,X88] :
      ( v1_xboole_0(X87)
      | ~ m1_subset_1(X88,X87)
      | k6_domain_1(X87,X88) = k1_tarski(X88) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_46,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_47,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_48,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_49,plain,(
    ! [X29,X30,X31,X32] : k3_enumset1(X29,X29,X30,X31,X32) = k2_enumset1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_50,plain,(
    ! [X33,X34,X35,X36,X37] : k4_enumset1(X33,X33,X34,X35,X36,X37) = k3_enumset1(X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_51,plain,(
    ! [X38,X39,X40,X41,X42,X43] : k5_enumset1(X38,X38,X39,X40,X41,X42,X43) = k4_enumset1(X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_52,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50] : k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50) = k5_enumset1(X44,X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X2)
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( v1_subset_1(k6_domain_1(esk5_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_59,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67,X68,X69,X70] :
      ( ( ~ r2_hidden(X60,X59)
        | X60 = X51
        | X60 = X52
        | X60 = X53
        | X60 = X54
        | X60 = X55
        | X60 = X56
        | X60 = X57
        | X60 = X58
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X51
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X52
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X53
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X54
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X55
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X56
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X57
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( X61 != X58
        | r2_hidden(X61,X59)
        | X59 != k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X62
        | ~ r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X63
        | ~ r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X64
        | ~ r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X65
        | ~ r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X66
        | ~ r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X67
        | ~ r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X68
        | ~ r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) != X69
        | ~ r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) )
      & ( r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)
        | esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X62
        | esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X63
        | esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X64
        | esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X65
        | esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X66
        | esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X67
        | esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X68
        | esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70) = X69
        | X70 = k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_60,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_63,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_64,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_69,negated_conjecture,
    ( v1_xboole_0(k6_domain_1(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])])).

fof(c_0_70,plain,(
    ! [X83,X84] :
      ( ~ r2_hidden(X83,X84)
      | ~ r1_tarski(X84,X83) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( k6_domain_1(X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( k6_domain_1(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_71])])).

cnf(c_0_76,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_43]),c_0_73]),c_0_44])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_38])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 16:12:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.14/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.028 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.14/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.14/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.37  fof(rc2_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&v1_xboole_0(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 0.14/0.37  fof(t6_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.14/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.37  fof(cc2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_xboole_0(X2))=>~(v1_subset_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 0.14/0.37  fof(cc4_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~(v1_subset_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 0.14/0.37  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.14/0.37  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.14/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.14/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.14/0.37  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.14/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.37  fof(c_0_20, plain, ![X80, X81, X82]:(~r2_hidden(X80,X81)|~m1_subset_1(X81,k1_zfmisc_1(X82))|~v1_xboole_0(X82)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.14/0.37  fof(c_0_21, plain, ![X74]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X74)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.14/0.37  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_23, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.37  fof(c_0_24, plain, ![X15, X16, X17, X18, X19]:((~r1_tarski(X15,X16)|(~r2_hidden(X17,X15)|r2_hidden(X17,X16)))&((r2_hidden(esk2_2(X18,X19),X18)|r1_tarski(X18,X19))&(~r2_hidden(esk2_2(X18,X19),X19)|r1_tarski(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.37  cnf(c_0_25, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.37  cnf(c_0_26, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  fof(c_0_27, plain, ![X72]:(m1_subset_1(esk4_1(X72),k1_zfmisc_1(X72))&v1_xboole_0(esk4_1(X72))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).
% 0.14/0.37  fof(c_0_28, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t6_tex_2])).
% 0.14/0.37  fof(c_0_29, plain, ![X21, X22]:(((r1_tarski(X21,X22)|X21!=X22)&(r1_tarski(X22,X21)|X21!=X22))&(~r1_tarski(X21,X22)|~r1_tarski(X22,X21)|X21=X22)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.37  cnf(c_0_30, plain, (r1_tarski(k1_xboole_0,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.37  cnf(c_0_31, plain, (v1_xboole_0(esk4_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.37  fof(c_0_32, plain, ![X11, X12, X13]:((~v1_xboole_0(X11)|~r2_hidden(X12,X11))&(r2_hidden(esk1_1(X13),X13)|v1_xboole_0(X13))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.37  fof(c_0_33, plain, ![X89, X90]:(v1_xboole_0(X89)|~v1_zfmisc_1(X89)|(~m1_subset_1(X90,k1_zfmisc_1(X89))|(v1_xboole_0(X90)|~v1_subset_1(X90,X89)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).
% 0.14/0.37  fof(c_0_34, plain, ![X75, X76]:(~v1_xboole_0(X75)|(~m1_subset_1(X76,k1_zfmisc_1(X75))|~v1_subset_1(X76,X75))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).
% 0.14/0.37  fof(c_0_35, plain, ![X85, X86]:(v1_xboole_0(X85)|~m1_subset_1(X86,X85)|m1_subset_1(k6_domain_1(X85,X86),k1_zfmisc_1(X85))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.14/0.37  fof(c_0_36, negated_conjecture, (~v1_xboole_0(esk5_0)&(m1_subset_1(esk6_0,esk5_0)&(v1_subset_1(k6_domain_1(esk5_0,esk6_0),esk5_0)&v1_zfmisc_1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).
% 0.14/0.37  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.37  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.14/0.37  cnf(c_0_39, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.37  cnf(c_0_40, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.37  cnf(c_0_41, plain, (~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.37  cnf(c_0_42, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.37  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.37  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.37  fof(c_0_45, plain, ![X87, X88]:(v1_xboole_0(X87)|~m1_subset_1(X88,X87)|k6_domain_1(X87,X88)=k1_tarski(X88)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.14/0.37  fof(c_0_46, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.37  fof(c_0_47, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.37  fof(c_0_48, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.37  fof(c_0_49, plain, ![X29, X30, X31, X32]:k3_enumset1(X29,X29,X30,X31,X32)=k2_enumset1(X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.37  fof(c_0_50, plain, ![X33, X34, X35, X36, X37]:k4_enumset1(X33,X33,X34,X35,X36,X37)=k3_enumset1(X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.37  fof(c_0_51, plain, ![X38, X39, X40, X41, X42, X43]:k5_enumset1(X38,X38,X39,X40,X41,X42,X43)=k4_enumset1(X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.14/0.37  fof(c_0_52, plain, ![X44, X45, X46, X47, X48, X49, X50]:k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50)=k5_enumset1(X44,X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.14/0.37  cnf(c_0_53, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.14/0.37  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_39, c_0_26])).
% 0.14/0.37  cnf(c_0_55, plain, (v1_xboole_0(X1)|~v1_zfmisc_1(X2)|~v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[c_0_40, c_0_41])).
% 0.14/0.37  cnf(c_0_56, negated_conjecture, (m1_subset_1(k6_domain_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.14/0.37  cnf(c_0_57, negated_conjecture, (v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.37  cnf(c_0_58, negated_conjecture, (v1_subset_1(k6_domain_1(esk5_0,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.37  fof(c_0_59, plain, ![X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67, X68, X69, X70]:(((~r2_hidden(X60,X59)|(X60=X51|X60=X52|X60=X53|X60=X54|X60=X55|X60=X56|X60=X57|X60=X58)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58))&((((((((X61!=X51|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58))&(X61!=X52|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(X61!=X53|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(X61!=X54|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(X61!=X55|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(X61!=X56|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(X61!=X57|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(X61!=X58|r2_hidden(X61,X59)|X59!=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58))))&(((((((((esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X62|~r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69))&(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X63|~r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X64|~r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X65|~r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X66|~r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X67|~r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X68|~r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)!=X69|~r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))&(r2_hidden(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70),X70)|(esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X62|esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X63|esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X64|esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X65|esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X66|esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X67|esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X68|esk3_9(X62,X63,X64,X65,X66,X67,X68,X69,X70)=X69)|X70=k6_enumset1(X62,X63,X64,X65,X66,X67,X68,X69)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.14/0.37  cnf(c_0_60, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.37  cnf(c_0_61, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.14/0.37  cnf(c_0_62, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.14/0.37  cnf(c_0_63, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.14/0.37  cnf(c_0_64, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.37  cnf(c_0_65, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.14/0.37  cnf(c_0_66, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.14/0.37  cnf(c_0_67, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.14/0.37  cnf(c_0_68, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.14/0.37  cnf(c_0_69, negated_conjecture, (v1_xboole_0(k6_domain_1(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58])])).
% 0.14/0.37  fof(c_0_70, plain, ![X83, X84]:(~r2_hidden(X83,X84)|~r1_tarski(X84,X83)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.37  cnf(c_0_71, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.14/0.37  cnf(c_0_72, plain, (k6_domain_1(X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63]), c_0_64]), c_0_65]), c_0_66]), c_0_67])).
% 0.14/0.37  cnf(c_0_73, negated_conjecture, (k6_domain_1(esk5_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.14/0.37  cnf(c_0_74, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.14/0.37  cnf(c_0_75, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_71])])).
% 0.14/0.37  cnf(c_0_76, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_43]), c_0_73]), c_0_44])).
% 0.14/0.37  cnf(c_0_77, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_38])).
% 0.14/0.37  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 79
% 0.14/0.37  # Proof object clause steps            : 38
% 0.14/0.37  # Proof object formula steps           : 41
% 0.14/0.37  # Proof object conjectures             : 12
% 0.14/0.37  # Proof object clause conjectures      : 9
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 23
% 0.14/0.37  # Proof object initial formulas used   : 20
% 0.14/0.37  # Proof object generating inferences   : 12
% 0.14/0.37  # Proof object simplifying inferences  : 17
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 21
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 47
% 0.14/0.37  # Removed in clause preprocessing      : 7
% 0.14/0.37  # Initial clauses in saturation        : 40
% 0.14/0.37  # Processed clauses                    : 128
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 19
% 0.14/0.37  # ...remaining for further processing  : 109
% 0.14/0.37  # Other redundant clauses eliminated   : 19
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 2
% 0.14/0.37  # Backward-rewritten                   : 8
% 0.14/0.37  # Generated clauses                    : 92
% 0.14/0.37  # ...of the previous two non-trivial   : 74
% 0.14/0.37  # Contextual simplify-reflections      : 1
% 0.14/0.37  # Paramodulations                      : 81
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 19
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 49
% 0.14/0.37  #    Positive orientable unit clauses  : 18
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 4
% 0.14/0.37  #    Non-unit-clauses                  : 27
% 0.14/0.37  # Current number of unprocessed clauses: 20
% 0.14/0.37  # ...number of literals in the above   : 76
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 56
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 238
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 152
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.14/0.37  # Unit Clause-clause subsumption calls : 18
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 62
% 0.14/0.37  # BW rewrite match successes           : 5
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 3977
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.032 s
% 0.14/0.37  # System time              : 0.005 s
% 0.14/0.37  # Total time               : 0.037 s
% 0.14/0.37  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
