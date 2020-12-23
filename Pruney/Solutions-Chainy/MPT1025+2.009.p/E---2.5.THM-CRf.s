%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:36 EST 2020

% Result     : Theorem 8.10s
% Output     : CNFRefutation 8.10s
% Verified   : 
% Statistics : Number of formulae       :  142 (1227 expanded)
%              Number of clauses        :   97 ( 572 expanded)
%              Number of leaves         :   22 ( 317 expanded)
%              Depth                    :   20
%              Number of atoms          :  499 (3874 expanded)
%              Number of equality atoms :   96 ( 520 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(d1_funct_1,axiom,(
    ! [X1] :
      ( v1_funct_1(X1)
    <=> ! [X2,X3,X4] :
          ( ( r2_hidden(k4_tarski(X2,X3),X1)
            & r2_hidden(k4_tarski(X2,X4),X1) )
         => X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t116_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ~ ( r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

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

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

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

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_22,plain,(
    ! [X69,X70,X71] :
      ( ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
      | v1_relat_1(X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_23,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_24,plain,(
    ! [X67,X68] :
      ( ~ r2_hidden(X67,X68)
      | ~ r1_tarski(X68,X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_25,plain,(
    ! [X19] : r1_tarski(k1_xboole_0,X19) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X32,X33,X34,X36] :
      ( ( r2_hidden(esk3_3(X32,X33,X34),k1_relat_1(X34))
        | ~ r2_hidden(X32,k9_relat_1(X34,X33))
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(k4_tarski(esk3_3(X32,X33,X34),X32),X34)
        | ~ r2_hidden(X32,k9_relat_1(X34,X33))
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(esk3_3(X32,X33,X34),X33)
        | ~ r2_hidden(X32,k9_relat_1(X34,X33))
        | ~ v1_relat_1(X34) )
      & ( ~ r2_hidden(X36,k1_relat_1(X34))
        | ~ r2_hidden(k4_tarski(X36,X32),X34)
        | ~ r2_hidden(X36,X33)
        | r2_hidden(X32,k9_relat_1(X34,X33))
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_32,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

fof(c_0_36,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_37,plain,(
    ! [X37,X38,X39,X40,X42,X43,X44,X45,X47] :
      ( ( r2_hidden(esk4_4(X37,X38,X39,X40),k1_relat_1(X37))
        | ~ r2_hidden(X40,X39)
        | X39 != k9_relat_1(X37,X38)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( r2_hidden(esk4_4(X37,X38,X39,X40),X38)
        | ~ r2_hidden(X40,X39)
        | X39 != k9_relat_1(X37,X38)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( X40 = k1_funct_1(X37,esk4_4(X37,X38,X39,X40))
        | ~ r2_hidden(X40,X39)
        | X39 != k9_relat_1(X37,X38)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( ~ r2_hidden(X43,k1_relat_1(X37))
        | ~ r2_hidden(X43,X38)
        | X42 != k1_funct_1(X37,X43)
        | r2_hidden(X42,X39)
        | X39 != k9_relat_1(X37,X38)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( ~ r2_hidden(esk5_3(X37,X44,X45),X45)
        | ~ r2_hidden(X47,k1_relat_1(X37))
        | ~ r2_hidden(X47,X44)
        | esk5_3(X37,X44,X45) != k1_funct_1(X37,X47)
        | X45 = k9_relat_1(X37,X44)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( r2_hidden(esk6_3(X37,X44,X45),k1_relat_1(X37))
        | r2_hidden(esk5_3(X37,X44,X45),X45)
        | X45 = k9_relat_1(X37,X44)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( r2_hidden(esk6_3(X37,X44,X45),X44)
        | r2_hidden(esk5_3(X37,X44,X45),X45)
        | X45 = k9_relat_1(X37,X44)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( esk5_3(X37,X44,X45) = k1_funct_1(X37,esk6_3(X37,X44,X45))
        | r2_hidden(esk5_3(X37,X44,X45),X45)
        | X45 = k9_relat_1(X37,X44)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_41,plain,(
    ! [X59,X60,X61,X62,X63] :
      ( ( ~ v1_funct_1(X59)
        | ~ r2_hidden(k4_tarski(X60,X61),X59)
        | ~ r2_hidden(k4_tarski(X60,X62),X59)
        | X61 = X62 )
      & ( r2_hidden(k4_tarski(esk10_1(X63),esk11_1(X63)),X63)
        | v1_funct_1(X63) )
      & ( r2_hidden(k4_tarski(esk10_1(X63),esk12_1(X63)),X63)
        | v1_funct_1(X63) )
      & ( esk11_1(X63) != esk12_1(X63)
        | v1_funct_1(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_1])])])])])])).

cnf(c_0_42,plain,
    ( r2_hidden(X4,X5)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k1_funct_1(X2,X1)
    | X5 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_29])).

cnf(c_0_44,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(esk10_1(X1),esk11_1(X1)),X1)
    | v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).

cnf(c_0_47,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_45])).

fof(c_0_49,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_35])]),c_0_33])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_52,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(esk1_1(k1_relat_1(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_40])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_51])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_57,plain,(
    ! [X75,X76,X77] :
      ( ~ v1_xboole_0(X75)
      | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))
      | v1_xboole_0(X77) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

fof(c_0_58,plain,(
    ! [X72,X73,X74] :
      ( ( v4_relat_1(X74,X72)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73))) )
      & ( v5_relat_1(X74,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_59,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ~ ( r2_hidden(X6,X3)
                      & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_funct_2])).

cnf(c_0_60,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),k1_relat_1(X1))
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_61,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_56])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_64,plain,(
    ! [X49,X50,X51,X53,X54,X55,X57] :
      ( ( r2_hidden(esk7_3(X49,X50,X51),k1_relat_1(X49))
        | ~ r2_hidden(X51,X50)
        | X50 != k2_relat_1(X49)
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49) )
      & ( X51 = k1_funct_1(X49,esk7_3(X49,X50,X51))
        | ~ r2_hidden(X51,X50)
        | X50 != k2_relat_1(X49)
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49) )
      & ( ~ r2_hidden(X54,k1_relat_1(X49))
        | X53 != k1_funct_1(X49,X54)
        | r2_hidden(X53,X50)
        | X50 != k2_relat_1(X49)
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49) )
      & ( ~ r2_hidden(esk8_2(X49,X55),X55)
        | ~ r2_hidden(X57,k1_relat_1(X49))
        | esk8_2(X49,X55) != k1_funct_1(X49,X57)
        | X55 = k2_relat_1(X49)
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49) )
      & ( r2_hidden(esk9_2(X49,X55),k1_relat_1(X49))
        | r2_hidden(esk8_2(X49,X55),X55)
        | X55 = k2_relat_1(X49)
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49) )
      & ( esk8_2(X49,X55) = k1_funct_1(X49,esk9_2(X49,X55))
        | r2_hidden(esk8_2(X49,X55),X55)
        | X55 = k2_relat_1(X49)
        | ~ v1_relat_1(X49)
        | ~ v1_funct_1(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_65,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_66,plain,(
    ! [X88,X89] :
      ( ( v1_funct_1(X89)
        | ~ r1_tarski(k2_relat_1(X89),X88)
        | ~ v1_relat_1(X89)
        | ~ v1_funct_1(X89) )
      & ( v1_funct_2(X89,k1_relat_1(X89),X88)
        | ~ r1_tarski(k2_relat_1(X89),X88)
        | ~ v1_relat_1(X89)
        | ~ v1_funct_1(X89) )
      & ( m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X89),X88)))
        | ~ r1_tarski(k2_relat_1(X89),X88)
        | ~ v1_relat_1(X89)
        | ~ v1_funct_1(X89) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

fof(c_0_67,negated_conjecture,(
    ! [X95] :
      ( v1_funct_1(esk16_0)
      & v1_funct_2(esk16_0,esk13_0,esk14_0)
      & m1_subset_1(esk16_0,k1_zfmisc_1(k2_zfmisc_1(esk13_0,esk14_0)))
      & r2_hidden(esk17_0,k7_relset_1(esk13_0,esk14_0,esk16_0,esk15_0))
      & ( ~ m1_subset_1(X95,esk13_0)
        | ~ r2_hidden(X95,esk15_0)
        | esk17_0 != k1_funct_1(esk16_0,X95) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_59])])])])).

fof(c_0_68,plain,(
    ! [X85,X86,X87] :
      ( ( ~ v1_funct_2(X87,X85,X86)
        | X85 = k1_relset_1(X85,X86,X87)
        | X86 = k1_xboole_0
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))) )
      & ( X85 != k1_relset_1(X85,X86,X87)
        | v1_funct_2(X87,X85,X86)
        | X86 = k1_xboole_0
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))) )
      & ( ~ v1_funct_2(X87,X85,X86)
        | X85 = k1_relset_1(X85,X86,X87)
        | X85 != k1_xboole_0
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))) )
      & ( X85 != k1_relset_1(X85,X86,X87)
        | v1_funct_2(X87,X85,X86)
        | X85 != k1_xboole_0
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))) )
      & ( ~ v1_funct_2(X87,X85,X86)
        | X87 = k1_xboole_0
        | X85 = k1_xboole_0
        | X86 != k1_xboole_0
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))) )
      & ( X87 != k1_xboole_0
        | v1_funct_2(X87,X85,X86)
        | X85 = k1_xboole_0
        | X86 != k1_xboole_0
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_48]),c_0_47]),c_0_61]),c_0_35])]),c_0_33])).

cnf(c_0_70,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_27])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_73,plain,(
    ! [X28,X29] :
      ( ( ~ v5_relat_1(X29,X28)
        | r1_tarski(k2_relat_1(X29),X28)
        | ~ v1_relat_1(X29) )
      & ( ~ r1_tarski(k2_relat_1(X29),X28)
        | v5_relat_1(X29,X28)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_74,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_27])).

fof(c_0_75,plain,(
    ! [X30,X31] : v1_relat_1(k2_zfmisc_1(X30,X31)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_76,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_hidden(X20,X22)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) )
      & ( r2_hidden(X21,X23)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) )
      & ( ~ r2_hidden(X20,X22)
        | ~ r2_hidden(X21,X23)
        | r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_78,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk16_0,k1_zfmisc_1(k2_zfmisc_1(esk13_0,esk14_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_80,plain,(
    ! [X78,X79,X80] :
      ( ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X78,X79)))
      | k1_relset_1(X78,X79,X80) = k1_relat_1(X80) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_81,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(esk16_0,esk13_0,esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_83,plain,
    ( X1 = k1_funct_1(X2,esk4_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_84,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_69])).

cnf(c_0_85,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_86,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_72])])).

cnf(c_0_87,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_88,plain,
    ( v5_relat_1(k2_zfmisc_1(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_71])).

cnf(c_0_89,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_91,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_93,negated_conjecture,
    ( v5_relat_1(esk16_0,esk14_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_79])).

cnf(c_0_94,negated_conjecture,
    ( v1_relat_1(esk16_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_79])).

cnf(c_0_95,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_96,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_97,negated_conjecture,
    ( k1_relset_1(esk13_0,esk14_0,esk16_0) = esk13_0
    | esk14_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_79]),c_0_82])])).

fof(c_0_98,plain,(
    ! [X81,X82,X83,X84] :
      ( ~ m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X81,X82)))
      | k7_relset_1(X81,X82,X83,X84) = k9_relat_1(X83,X84) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_99,negated_conjecture,
    ( ~ m1_subset_1(X1,esk13_0)
    | ~ r2_hidden(X1,esk15_0)
    | esk17_0 != k1_funct_1(esk16_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_100,plain,
    ( k1_funct_1(X1,esk4_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_101,negated_conjecture,
    ( v1_funct_1(esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_102,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | m1_subset_1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_103,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_104,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_51])).

cnf(c_0_105,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_86])).

cnf(c_0_106,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])])).

cnf(c_0_107,plain,
    ( v1_funct_1(k2_zfmisc_1(X1,X2))
    | r2_hidden(esk11_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_45])).

cnf(c_0_108,plain,
    ( r2_hidden(X1,k2_zfmisc_1(k1_relat_1(X2),X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk16_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_93]),c_0_94])])).

cnf(c_0_110,plain,
    ( r2_hidden(esk4_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_95])).

cnf(c_0_111,negated_conjecture,
    ( k1_relat_1(esk16_0) = esk13_0
    | esk14_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_79])])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(esk17_0,k7_relset_1(esk13_0,esk14_0,esk16_0,esk15_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_113,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_114,negated_conjecture,
    ( ~ m1_subset_1(esk4_4(esk16_0,X1,k9_relat_1(esk16_0,X1),esk17_0),esk13_0)
    | ~ r2_hidden(esk4_4(esk16_0,X1,k9_relat_1(esk16_0,X1),esk17_0),esk15_0)
    | ~ r2_hidden(esk17_0,k9_relat_1(esk16_0,X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101]),c_0_94])])])).

cnf(c_0_115,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_116,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_117,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_118,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_69])).

cnf(c_0_119,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_106])).

cnf(c_0_120,plain,
    ( v1_funct_1(k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_107])).

cnf(c_0_121,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk16_0),esk14_0))
    | ~ r2_hidden(X1,esk16_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_101]),c_0_94])])).

cnf(c_0_123,negated_conjecture,
    ( esk14_0 = k1_xboole_0
    | r2_hidden(esk4_4(esk16_0,X1,k9_relat_1(esk16_0,X1),X2),esk13_0)
    | ~ r2_hidden(X2,k9_relat_1(esk16_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_101]),c_0_94])])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk17_0,k9_relat_1(esk16_0,esk15_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_79])])).

cnf(c_0_125,negated_conjecture,
    ( ~ r2_hidden(esk4_4(esk16_0,X1,k9_relat_1(esk16_0,X1),esk17_0),esk15_0)
    | ~ r2_hidden(esk4_4(esk16_0,X1,k9_relat_1(esk16_0,X1),esk17_0),esk13_0)
    | ~ r2_hidden(esk17_0,k9_relat_1(esk16_0,X1)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_126,plain,
    ( r2_hidden(esk4_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_116])).

cnf(c_0_127,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_117]),c_0_104])])).

cnf(c_0_128,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120]),c_0_89]),c_0_104])])).

cnf(c_0_129,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_34])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(esk16_0),esk14_0))
    | ~ r2_hidden(esk2_2(X1,k2_zfmisc_1(k1_relat_1(esk16_0),esk14_0)),esk16_0) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_131,negated_conjecture,
    ( esk14_0 = k1_xboole_0
    | r2_hidden(esk4_4(esk16_0,esk15_0,k9_relat_1(esk16_0,esk15_0),esk17_0),esk13_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_132,negated_conjecture,
    ( ~ r2_hidden(esk4_4(esk16_0,esk15_0,k9_relat_1(esk16_0,esk15_0),esk17_0),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_124]),c_0_101]),c_0_94])])).

cnf(c_0_133,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_127])).

cnf(c_0_134,plain,
    ( m1_subset_1(k2_zfmisc_1(X1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_128]),c_0_117]),c_0_120]),c_0_89]),c_0_119]),c_0_29])])).

cnf(c_0_135,negated_conjecture,
    ( ~ v1_xboole_0(esk16_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_124]),c_0_94])])).

cnf(c_0_136,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_117]),c_0_104])])).

cnf(c_0_137,negated_conjecture,
    ( r1_tarski(esk16_0,k2_zfmisc_1(k1_relat_1(esk16_0),esk14_0)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_40])).

cnf(c_0_138,negated_conjecture,
    ( esk14_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_139,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_140,negated_conjecture,
    ( ~ r1_tarski(esk16_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_141,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_138]),c_0_139]),c_0_140]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 8.10/8.29  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 8.10/8.29  # and selection function SelectComplexExceptUniqMaxHorn.
% 8.10/8.29  #
% 8.10/8.29  # Preprocessing time       : 0.030 s
% 8.10/8.29  # Presaturation interreduction done
% 8.10/8.29  
% 8.10/8.29  # Proof found!
% 8.10/8.29  # SZS status Theorem
% 8.10/8.29  # SZS output start CNFRefutation
% 8.10/8.29  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.10/8.29  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.10/8.29  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.10/8.29  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.10/8.29  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 8.10/8.29  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.10/8.29  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.10/8.29  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 8.10/8.29  fof(d1_funct_1, axiom, ![X1]:(v1_funct_1(X1)<=>![X2, X3, X4]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X2,X4),X1))=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_1)).
% 8.10/8.29  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.10/8.29  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 8.10/8.29  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.10/8.29  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 8.10/8.29  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 8.10/8.29  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 8.10/8.29  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.10/8.29  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.10/8.29  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.10/8.29  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 8.10/8.29  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.10/8.29  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.10/8.29  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 8.10/8.29  fof(c_0_22, plain, ![X69, X70, X71]:(~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))|v1_relat_1(X71)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 8.10/8.29  fof(c_0_23, plain, ![X26, X27]:((~m1_subset_1(X26,k1_zfmisc_1(X27))|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|m1_subset_1(X26,k1_zfmisc_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 8.10/8.29  fof(c_0_24, plain, ![X67, X68]:(~r2_hidden(X67,X68)|~r1_tarski(X68,X67)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 8.10/8.29  fof(c_0_25, plain, ![X19]:r1_tarski(k1_xboole_0,X19), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 8.10/8.29  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 8.10/8.29  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 8.10/8.29  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 8.10/8.29  cnf(c_0_29, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 8.10/8.29  fof(c_0_30, plain, ![X32, X33, X34, X36]:((((r2_hidden(esk3_3(X32,X33,X34),k1_relat_1(X34))|~r2_hidden(X32,k9_relat_1(X34,X33))|~v1_relat_1(X34))&(r2_hidden(k4_tarski(esk3_3(X32,X33,X34),X32),X34)|~r2_hidden(X32,k9_relat_1(X34,X33))|~v1_relat_1(X34)))&(r2_hidden(esk3_3(X32,X33,X34),X33)|~r2_hidden(X32,k9_relat_1(X34,X33))|~v1_relat_1(X34)))&(~r2_hidden(X36,k1_relat_1(X34))|~r2_hidden(k4_tarski(X36,X32),X34)|~r2_hidden(X36,X33)|r2_hidden(X32,k9_relat_1(X34,X33))|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 8.10/8.29  cnf(c_0_31, plain, (v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 8.10/8.29  fof(c_0_32, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 8.10/8.29  cnf(c_0_33, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 8.10/8.29  cnf(c_0_34, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 8.10/8.29  cnf(c_0_35, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 8.10/8.29  fof(c_0_36, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 8.10/8.29  fof(c_0_37, plain, ![X37, X38, X39, X40, X42, X43, X44, X45, X47]:(((((r2_hidden(esk4_4(X37,X38,X39,X40),k1_relat_1(X37))|~r2_hidden(X40,X39)|X39!=k9_relat_1(X37,X38)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(r2_hidden(esk4_4(X37,X38,X39,X40),X38)|~r2_hidden(X40,X39)|X39!=k9_relat_1(X37,X38)|(~v1_relat_1(X37)|~v1_funct_1(X37))))&(X40=k1_funct_1(X37,esk4_4(X37,X38,X39,X40))|~r2_hidden(X40,X39)|X39!=k9_relat_1(X37,X38)|(~v1_relat_1(X37)|~v1_funct_1(X37))))&(~r2_hidden(X43,k1_relat_1(X37))|~r2_hidden(X43,X38)|X42!=k1_funct_1(X37,X43)|r2_hidden(X42,X39)|X39!=k9_relat_1(X37,X38)|(~v1_relat_1(X37)|~v1_funct_1(X37))))&((~r2_hidden(esk5_3(X37,X44,X45),X45)|(~r2_hidden(X47,k1_relat_1(X37))|~r2_hidden(X47,X44)|esk5_3(X37,X44,X45)!=k1_funct_1(X37,X47))|X45=k9_relat_1(X37,X44)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(((r2_hidden(esk6_3(X37,X44,X45),k1_relat_1(X37))|r2_hidden(esk5_3(X37,X44,X45),X45)|X45=k9_relat_1(X37,X44)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(r2_hidden(esk6_3(X37,X44,X45),X44)|r2_hidden(esk5_3(X37,X44,X45),X45)|X45=k9_relat_1(X37,X44)|(~v1_relat_1(X37)|~v1_funct_1(X37))))&(esk5_3(X37,X44,X45)=k1_funct_1(X37,esk6_3(X37,X44,X45))|r2_hidden(esk5_3(X37,X44,X45),X45)|X45=k9_relat_1(X37,X44)|(~v1_relat_1(X37)|~v1_funct_1(X37)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 8.10/8.29  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 8.10/8.29  cnf(c_0_39, plain, (~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 8.10/8.29  cnf(c_0_40, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 8.10/8.29  fof(c_0_41, plain, ![X59, X60, X61, X62, X63]:((~v1_funct_1(X59)|(~r2_hidden(k4_tarski(X60,X61),X59)|~r2_hidden(k4_tarski(X60,X62),X59)|X61=X62))&(((r2_hidden(k4_tarski(esk10_1(X63),esk11_1(X63)),X63)|v1_funct_1(X63))&(r2_hidden(k4_tarski(esk10_1(X63),esk12_1(X63)),X63)|v1_funct_1(X63)))&(esk11_1(X63)!=esk12_1(X63)|v1_funct_1(X63)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_1])])])])])])).
% 8.10/8.29  cnf(c_0_42, plain, (r2_hidden(X4,X5)|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X4!=k1_funct_1(X2,X1)|X5!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 8.10/8.29  cnf(c_0_43, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_29])).
% 8.10/8.29  cnf(c_0_44, plain, (r1_tarski(k9_relat_1(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 8.10/8.29  cnf(c_0_45, plain, (r2_hidden(k4_tarski(esk10_1(X1),esk11_1(X1)),X1)|v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 8.10/8.29  cnf(c_0_46, plain, (r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X2,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).
% 8.10/8.29  cnf(c_0_47, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 8.10/8.29  cnf(c_0_48, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_45])).
% 8.10/8.29  fof(c_0_49, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 8.10/8.29  cnf(c_0_50, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_35])]), c_0_33])).
% 8.10/8.29  cnf(c_0_51, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 8.10/8.29  cnf(c_0_52, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 8.10/8.29  cnf(c_0_53, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))|~r2_hidden(esk1_1(k1_relat_1(k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 8.10/8.29  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_40])).
% 8.10/8.29  cnf(c_0_55, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_53, c_0_51])).
% 8.10/8.29  cnf(c_0_56, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 8.10/8.29  fof(c_0_57, plain, ![X75, X76, X77]:(~v1_xboole_0(X75)|(~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))|v1_xboole_0(X77))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 8.10/8.29  fof(c_0_58, plain, ![X72, X73, X74]:((v4_relat_1(X74,X72)|~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73))))&(v5_relat_1(X74,X73)|~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 8.10/8.29  fof(c_0_59, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 8.10/8.29  cnf(c_0_60, plain, (r2_hidden(esk6_3(X1,X2,X3),k1_relat_1(X1))|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 8.10/8.29  cnf(c_0_61, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_56])).
% 8.10/8.29  cnf(c_0_62, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 8.10/8.29  cnf(c_0_63, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 8.10/8.29  fof(c_0_64, plain, ![X49, X50, X51, X53, X54, X55, X57]:((((r2_hidden(esk7_3(X49,X50,X51),k1_relat_1(X49))|~r2_hidden(X51,X50)|X50!=k2_relat_1(X49)|(~v1_relat_1(X49)|~v1_funct_1(X49)))&(X51=k1_funct_1(X49,esk7_3(X49,X50,X51))|~r2_hidden(X51,X50)|X50!=k2_relat_1(X49)|(~v1_relat_1(X49)|~v1_funct_1(X49))))&(~r2_hidden(X54,k1_relat_1(X49))|X53!=k1_funct_1(X49,X54)|r2_hidden(X53,X50)|X50!=k2_relat_1(X49)|(~v1_relat_1(X49)|~v1_funct_1(X49))))&((~r2_hidden(esk8_2(X49,X55),X55)|(~r2_hidden(X57,k1_relat_1(X49))|esk8_2(X49,X55)!=k1_funct_1(X49,X57))|X55=k2_relat_1(X49)|(~v1_relat_1(X49)|~v1_funct_1(X49)))&((r2_hidden(esk9_2(X49,X55),k1_relat_1(X49))|r2_hidden(esk8_2(X49,X55),X55)|X55=k2_relat_1(X49)|(~v1_relat_1(X49)|~v1_funct_1(X49)))&(esk8_2(X49,X55)=k1_funct_1(X49,esk9_2(X49,X55))|r2_hidden(esk8_2(X49,X55),X55)|X55=k2_relat_1(X49)|(~v1_relat_1(X49)|~v1_funct_1(X49)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 8.10/8.29  cnf(c_0_65, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 8.10/8.29  fof(c_0_66, plain, ![X88, X89]:(((v1_funct_1(X89)|~r1_tarski(k2_relat_1(X89),X88)|(~v1_relat_1(X89)|~v1_funct_1(X89)))&(v1_funct_2(X89,k1_relat_1(X89),X88)|~r1_tarski(k2_relat_1(X89),X88)|(~v1_relat_1(X89)|~v1_funct_1(X89))))&(m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X89),X88)))|~r1_tarski(k2_relat_1(X89),X88)|(~v1_relat_1(X89)|~v1_funct_1(X89)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 8.10/8.29  fof(c_0_67, negated_conjecture, ![X95]:(((v1_funct_1(esk16_0)&v1_funct_2(esk16_0,esk13_0,esk14_0))&m1_subset_1(esk16_0,k1_zfmisc_1(k2_zfmisc_1(esk13_0,esk14_0))))&(r2_hidden(esk17_0,k7_relset_1(esk13_0,esk14_0,esk16_0,esk15_0))&(~m1_subset_1(X95,esk13_0)|(~r2_hidden(X95,esk15_0)|esk17_0!=k1_funct_1(esk16_0,X95))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_59])])])])).
% 8.10/8.29  fof(c_0_68, plain, ![X85, X86, X87]:((((~v1_funct_2(X87,X85,X86)|X85=k1_relset_1(X85,X86,X87)|X86=k1_xboole_0|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))))&(X85!=k1_relset_1(X85,X86,X87)|v1_funct_2(X87,X85,X86)|X86=k1_xboole_0|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86)))))&((~v1_funct_2(X87,X85,X86)|X85=k1_relset_1(X85,X86,X87)|X85!=k1_xboole_0|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))))&(X85!=k1_relset_1(X85,X86,X87)|v1_funct_2(X87,X85,X86)|X85!=k1_xboole_0|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))))))&((~v1_funct_2(X87,X85,X86)|X87=k1_xboole_0|X85=k1_xboole_0|X86!=k1_xboole_0|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))))&(X87!=k1_xboole_0|v1_funct_2(X87,X85,X86)|X85=k1_xboole_0|X86!=k1_xboole_0|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 8.10/8.29  cnf(c_0_69, plain, (X1=k1_xboole_0|r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_48]), c_0_47]), c_0_61]), c_0_35])]), c_0_33])).
% 8.10/8.29  cnf(c_0_70, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_62, c_0_27])).
% 8.10/8.29  cnf(c_0_71, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_63])).
% 8.10/8.29  cnf(c_0_72, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 8.10/8.29  fof(c_0_73, plain, ![X28, X29]:((~v5_relat_1(X29,X28)|r1_tarski(k2_relat_1(X29),X28)|~v1_relat_1(X29))&(~r1_tarski(k2_relat_1(X29),X28)|v5_relat_1(X29,X28)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 8.10/8.29  cnf(c_0_74, plain, (v5_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_65, c_0_27])).
% 8.10/8.29  fof(c_0_75, plain, ![X30, X31]:v1_relat_1(k2_zfmisc_1(X30,X31)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 8.10/8.29  fof(c_0_76, plain, ![X20, X21, X22, X23]:(((r2_hidden(X20,X22)|~r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)))&(r2_hidden(X21,X23)|~r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23))))&(~r2_hidden(X20,X22)|~r2_hidden(X21,X23)|r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 8.10/8.29  cnf(c_0_77, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 8.10/8.29  cnf(c_0_78, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 8.10/8.29  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk16_0,k1_zfmisc_1(k2_zfmisc_1(esk13_0,esk14_0)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 8.10/8.29  fof(c_0_80, plain, ![X78, X79, X80]:(~m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X78,X79)))|k1_relset_1(X78,X79,X80)=k1_relat_1(X80)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 8.10/8.29  cnf(c_0_81, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 8.10/8.29  cnf(c_0_82, negated_conjecture, (v1_funct_2(esk16_0,esk13_0,esk14_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 8.10/8.29  cnf(c_0_83, plain, (X1=k1_funct_1(X2,esk4_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 8.10/8.29  cnf(c_0_84, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_69])).
% 8.10/8.29  cnf(c_0_85, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 8.10/8.29  cnf(c_0_86, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_72])])).
% 8.10/8.29  cnf(c_0_87, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 8.10/8.29  cnf(c_0_88, plain, (v5_relat_1(k2_zfmisc_1(X1,X2),X2)), inference(spm,[status(thm)],[c_0_74, c_0_71])).
% 8.10/8.29  cnf(c_0_89, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 8.10/8.29  cnf(c_0_90, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 8.10/8.29  cnf(c_0_91, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 8.10/8.29  cnf(c_0_92, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 8.10/8.29  cnf(c_0_93, negated_conjecture, (v5_relat_1(esk16_0,esk14_0)), inference(spm,[status(thm)],[c_0_65, c_0_79])).
% 8.10/8.29  cnf(c_0_94, negated_conjecture, (v1_relat_1(esk16_0)), inference(spm,[status(thm)],[c_0_26, c_0_79])).
% 8.10/8.29  cnf(c_0_95, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),k1_relat_1(X1))|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 8.10/8.29  cnf(c_0_96, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 8.10/8.29  cnf(c_0_97, negated_conjecture, (k1_relset_1(esk13_0,esk14_0,esk16_0)=esk13_0|esk14_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_79]), c_0_82])])).
% 8.10/8.29  fof(c_0_98, plain, ![X81, X82, X83, X84]:(~m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X81,X82)))|k7_relset_1(X81,X82,X83,X84)=k9_relat_1(X83,X84)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 8.10/8.29  cnf(c_0_99, negated_conjecture, (~m1_subset_1(X1,esk13_0)|~r2_hidden(X1,esk15_0)|esk17_0!=k1_funct_1(esk16_0,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 8.10/8.29  cnf(c_0_100, plain, (k1_funct_1(X1,esk4_4(X1,X2,k9_relat_1(X1,X2),X3))=X3|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_83])).
% 8.10/8.29  cnf(c_0_101, negated_conjecture, (v1_funct_1(esk16_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 8.10/8.29  fof(c_0_102, plain, ![X24, X25]:(~r2_hidden(X24,X25)|m1_subset_1(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 8.10/8.29  cnf(c_0_103, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 8.10/8.29  cnf(c_0_104, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_51])).
% 8.10/8.29  cnf(c_0_105, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_52, c_0_86])).
% 8.10/8.29  cnf(c_0_106, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])])).
% 8.10/8.29  cnf(c_0_107, plain, (v1_funct_1(k2_zfmisc_1(X1,X2))|r2_hidden(esk11_1(k2_zfmisc_1(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_90, c_0_45])).
% 8.10/8.29  cnf(c_0_108, plain, (r2_hidden(X1,k2_zfmisc_1(k1_relat_1(X2),X3))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X2),X3)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 8.10/8.29  cnf(c_0_109, negated_conjecture, (r1_tarski(k2_relat_1(esk16_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_93]), c_0_94])])).
% 8.10/8.29  cnf(c_0_110, plain, (r2_hidden(esk4_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_95])).
% 8.10/8.29  cnf(c_0_111, negated_conjecture, (k1_relat_1(esk16_0)=esk13_0|esk14_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_79])])).
% 8.10/8.29  cnf(c_0_112, negated_conjecture, (r2_hidden(esk17_0,k7_relset_1(esk13_0,esk14_0,esk16_0,esk15_0))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 8.10/8.29  cnf(c_0_113, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 8.10/8.29  cnf(c_0_114, negated_conjecture, (~m1_subset_1(esk4_4(esk16_0,X1,k9_relat_1(esk16_0,X1),esk17_0),esk13_0)|~r2_hidden(esk4_4(esk16_0,X1,k9_relat_1(esk16_0,X1),esk17_0),esk15_0)|~r2_hidden(esk17_0,k9_relat_1(esk16_0,X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101]), c_0_94])])])).
% 8.10/8.29  cnf(c_0_115, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 8.10/8.29  cnf(c_0_116, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 8.10/8.29  cnf(c_0_117, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 8.10/8.29  cnf(c_0_118, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_105, c_0_69])).
% 8.10/8.29  cnf(c_0_119, plain, (k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_106])).
% 8.10/8.29  cnf(c_0_120, plain, (v1_funct_1(k2_zfmisc_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_33, c_0_107])).
% 8.10/8.29  cnf(c_0_121, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 8.10/8.29  cnf(c_0_122, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk16_0),esk14_0))|~r2_hidden(X1,esk16_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_101]), c_0_94])])).
% 8.10/8.29  cnf(c_0_123, negated_conjecture, (esk14_0=k1_xboole_0|r2_hidden(esk4_4(esk16_0,X1,k9_relat_1(esk16_0,X1),X2),esk13_0)|~r2_hidden(X2,k9_relat_1(esk16_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_101]), c_0_94])])).
% 8.10/8.29  cnf(c_0_124, negated_conjecture, (r2_hidden(esk17_0,k9_relat_1(esk16_0,esk15_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_79])])).
% 8.10/8.29  cnf(c_0_125, negated_conjecture, (~r2_hidden(esk4_4(esk16_0,X1,k9_relat_1(esk16_0,X1),esk17_0),esk15_0)|~r2_hidden(esk4_4(esk16_0,X1,k9_relat_1(esk16_0,X1),esk17_0),esk13_0)|~r2_hidden(esk17_0,k9_relat_1(esk16_0,X1))), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 8.10/8.29  cnf(c_0_126, plain, (r2_hidden(esk4_4(X1,X2,k9_relat_1(X1,X2),X3),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_116])).
% 8.10/8.29  cnf(c_0_127, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_117]), c_0_104])])).
% 8.10/8.29  cnf(c_0_128, plain, (k1_relat_1(k2_zfmisc_1(X1,k1_xboole_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_120]), c_0_89]), c_0_104])])).
% 8.10/8.29  cnf(c_0_129, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_34])).
% 8.10/8.29  cnf(c_0_130, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(esk16_0),esk14_0))|~r2_hidden(esk2_2(X1,k2_zfmisc_1(k1_relat_1(esk16_0),esk14_0)),esk16_0)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 8.10/8.29  cnf(c_0_131, negated_conjecture, (esk14_0=k1_xboole_0|r2_hidden(esk4_4(esk16_0,esk15_0,k9_relat_1(esk16_0,esk15_0),esk17_0),esk13_0)), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 8.10/8.29  cnf(c_0_132, negated_conjecture, (~r2_hidden(esk4_4(esk16_0,esk15_0,k9_relat_1(esk16_0,esk15_0),esk17_0),esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_124]), c_0_101]), c_0_94])])).
% 8.10/8.29  cnf(c_0_133, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_84, c_0_127])).
% 8.10/8.29  cnf(c_0_134, plain, (m1_subset_1(k2_zfmisc_1(X1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_128]), c_0_117]), c_0_120]), c_0_89]), c_0_119]), c_0_29])])).
% 8.10/8.29  cnf(c_0_135, negated_conjecture, (~v1_xboole_0(esk16_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_124]), c_0_94])])).
% 8.10/8.29  cnf(c_0_136, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_117]), c_0_104])])).
% 8.10/8.29  cnf(c_0_137, negated_conjecture, (r1_tarski(esk16_0,k2_zfmisc_1(k1_relat_1(esk16_0),esk14_0))), inference(spm,[status(thm)],[c_0_130, c_0_40])).
% 8.10/8.29  cnf(c_0_138, negated_conjecture, (esk14_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_131, c_0_132])).
% 8.10/8.29  cnf(c_0_139, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 8.10/8.29  cnf(c_0_140, negated_conjecture, (~r1_tarski(esk16_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 8.10/8.29  cnf(c_0_141, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137, c_0_138]), c_0_139]), c_0_140]), ['proof']).
% 8.10/8.29  # SZS output end CNFRefutation
% 8.10/8.29  # Proof object total steps             : 142
% 8.10/8.29  # Proof object clause steps            : 97
% 8.10/8.29  # Proof object formula steps           : 45
% 8.10/8.29  # Proof object conjectures             : 26
% 8.10/8.29  # Proof object clause conjectures      : 23
% 8.10/8.29  # Proof object formula conjectures     : 3
% 8.10/8.29  # Proof object initial clauses used    : 35
% 8.10/8.29  # Proof object initial formulas used   : 22
% 8.10/8.29  # Proof object generating inferences   : 54
% 8.10/8.29  # Proof object simplifying inferences  : 63
% 8.10/8.29  # Training examples: 0 positive, 0 negative
% 8.10/8.29  # Parsed axioms                        : 22
% 8.10/8.29  # Removed by relevancy pruning/SinE    : 0
% 8.10/8.29  # Initial clauses                      : 61
% 8.10/8.29  # Removed in clause preprocessing      : 1
% 8.10/8.29  # Initial clauses in saturation        : 60
% 8.10/8.29  # Processed clauses                    : 33464
% 8.10/8.29  # ...of these trivial                  : 24
% 8.10/8.29  # ...subsumed                          : 29912
% 8.10/8.29  # ...remaining for further processing  : 3528
% 8.10/8.29  # Other redundant clauses eliminated   : 29
% 8.10/8.29  # Clauses deleted for lack of memory   : 0
% 8.10/8.29  # Backward-subsumed                    : 136
% 8.10/8.29  # Backward-rewritten                   : 570
% 8.10/8.29  # Generated clauses                    : 399659
% 8.10/8.29  # ...of the previous two non-trivial   : 301889
% 8.10/8.29  # Contextual simplify-reflections      : 355
% 8.10/8.29  # Paramodulations                      : 399631
% 8.10/8.29  # Factorizations                       : 0
% 8.10/8.29  # Equation resolutions                 : 29
% 8.10/8.29  # Propositional unsat checks           : 0
% 8.10/8.29  #    Propositional check models        : 0
% 8.10/8.29  #    Propositional check unsatisfiable : 0
% 8.10/8.29  #    Propositional clauses             : 0
% 8.10/8.29  #    Propositional clauses after purity: 0
% 8.10/8.29  #    Propositional unsat core size     : 0
% 8.10/8.29  #    Propositional preprocessing time  : 0.000
% 8.10/8.29  #    Propositional encoding time       : 0.000
% 8.10/8.29  #    Propositional solver time         : 0.000
% 8.10/8.29  #    Success case prop preproc time    : 0.000
% 8.10/8.29  #    Success case prop encoding time   : 0.000
% 8.10/8.29  #    Success case prop solver time     : 0.000
% 8.10/8.29  # Current number of processed clauses  : 2748
% 8.10/8.29  #    Positive orientable unit clauses  : 47
% 8.10/8.29  #    Positive unorientable unit clauses: 0
% 8.10/8.29  #    Negative unit clauses             : 39
% 8.10/8.29  #    Non-unit-clauses                  : 2662
% 8.10/8.29  # Current number of unprocessed clauses: 267864
% 8.10/8.29  # ...number of literals in the above   : 1297324
% 8.10/8.29  # Current number of archived formulas  : 0
% 8.10/8.29  # Current number of archived clauses   : 767
% 8.10/8.29  # Clause-clause subsumption calls (NU) : 2025289
% 8.10/8.29  # Rec. Clause-clause subsumption calls : 761970
% 8.10/8.29  # Non-unit clause-clause subsumptions  : 9269
% 8.10/8.29  # Unit Clause-clause subsumption calls : 24368
% 8.10/8.29  # Rewrite failures with RHS unbound    : 0
% 8.10/8.29  # BW rewrite match attempts            : 46
% 8.10/8.29  # BW rewrite match successes           : 23
% 8.10/8.29  # Condensation attempts                : 0
% 8.10/8.29  # Condensation successes               : 0
% 8.10/8.29  # Termbank termtop insertions          : 7836321
% 8.10/8.30  
% 8.10/8.30  # -------------------------------------------------
% 8.10/8.30  # User time                : 7.718 s
% 8.10/8.30  # System time              : 0.245 s
% 8.10/8.30  # Total time               : 7.963 s
% 8.10/8.30  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
