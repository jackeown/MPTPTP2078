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
% DateTime   : Thu Dec  3 11:01:26 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 (1385 expanded)
%              Number of clauses        :   72 ( 593 expanded)
%              Number of leaves         :   19 ( 338 expanded)
%              Depth                    :   16
%              Number of atoms          :  313 (4765 expanded)
%              Number of equality atoms :  143 (1698 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t96_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k3_xboole_0(X2,k2_zfmisc_1(X1,k2_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t11_funct_2])).

fof(c_0_20,plain,(
    ! [X67,X68,X69] :
      ( ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
      | k1_relset_1(X67,X68,X69) = k1_relat_1(X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk13_0)
    & v1_funct_2(esk13_0,esk11_0,esk12_0)
    & m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0)))
    & ( esk12_0 != k1_xboole_0
      | esk11_0 = k1_xboole_0 )
    & ~ r2_hidden(esk13_0,k1_funct_2(esk11_0,esk12_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_22,plain,(
    ! [X83,X84,X85,X86,X88,X89,X90,X91,X92,X94] :
      ( ( v1_relat_1(esk8_4(X83,X84,X85,X86))
        | ~ r2_hidden(X86,X85)
        | X85 != k1_funct_2(X83,X84) )
      & ( v1_funct_1(esk8_4(X83,X84,X85,X86))
        | ~ r2_hidden(X86,X85)
        | X85 != k1_funct_2(X83,X84) )
      & ( X86 = esk8_4(X83,X84,X85,X86)
        | ~ r2_hidden(X86,X85)
        | X85 != k1_funct_2(X83,X84) )
      & ( k1_relat_1(esk8_4(X83,X84,X85,X86)) = X83
        | ~ r2_hidden(X86,X85)
        | X85 != k1_funct_2(X83,X84) )
      & ( r1_tarski(k2_relat_1(esk8_4(X83,X84,X85,X86)),X84)
        | ~ r2_hidden(X86,X85)
        | X85 != k1_funct_2(X83,X84) )
      & ( ~ v1_relat_1(X89)
        | ~ v1_funct_1(X89)
        | X88 != X89
        | k1_relat_1(X89) != X83
        | ~ r1_tarski(k2_relat_1(X89),X84)
        | r2_hidden(X88,X85)
        | X85 != k1_funct_2(X83,X84) )
      & ( ~ r2_hidden(esk9_3(X90,X91,X92),X92)
        | ~ v1_relat_1(X94)
        | ~ v1_funct_1(X94)
        | esk9_3(X90,X91,X92) != X94
        | k1_relat_1(X94) != X90
        | ~ r1_tarski(k2_relat_1(X94),X91)
        | X92 = k1_funct_2(X90,X91) )
      & ( v1_relat_1(esk10_3(X90,X91,X92))
        | r2_hidden(esk9_3(X90,X91,X92),X92)
        | X92 = k1_funct_2(X90,X91) )
      & ( v1_funct_1(esk10_3(X90,X91,X92))
        | r2_hidden(esk9_3(X90,X91,X92),X92)
        | X92 = k1_funct_2(X90,X91) )
      & ( esk9_3(X90,X91,X92) = esk10_3(X90,X91,X92)
        | r2_hidden(esk9_3(X90,X91,X92),X92)
        | X92 = k1_funct_2(X90,X91) )
      & ( k1_relat_1(esk10_3(X90,X91,X92)) = X90
        | r2_hidden(esk9_3(X90,X91,X92),X92)
        | X92 = k1_funct_2(X90,X91) )
      & ( r1_tarski(k2_relat_1(esk10_3(X90,X91,X92)),X91)
        | r2_hidden(esk9_3(X90,X91,X92),X92)
        | X92 = k1_funct_2(X90,X91) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_23,plain,(
    ! [X80,X81,X82] :
      ( ( ~ v1_funct_2(X82,X80,X81)
        | X80 = k1_relset_1(X80,X81,X82)
        | X81 = k1_xboole_0
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( X80 != k1_relset_1(X80,X81,X82)
        | v1_funct_2(X82,X80,X81)
        | X81 = k1_xboole_0
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( ~ v1_funct_2(X82,X80,X81)
        | X80 = k1_relset_1(X80,X81,X82)
        | X80 != k1_xboole_0
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( X80 != k1_relset_1(X80,X81,X82)
        | v1_funct_2(X82,X80,X81)
        | X80 != k1_xboole_0
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( ~ v1_funct_2(X82,X80,X81)
        | X82 = k1_xboole_0
        | X80 = k1_xboole_0
        | X81 != k1_xboole_0
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( X82 != k1_xboole_0
        | v1_funct_2(X82,X80,X81)
        | X80 = k1_xboole_0
        | X81 != k1_xboole_0
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_24,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X55,X56,X57] :
      ( ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))
      | v1_relat_1(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_27,plain,(
    ! [X58,X59,X60] :
      ( ( v4_relat_1(X60,X58)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) )
      & ( v5_relat_1(X60,X59)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X2,X5)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X2 != X1
    | k1_relat_1(X1) != X3
    | ~ r1_tarski(k2_relat_1(X1),X4)
    | X5 != k1_funct_2(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k1_relset_1(esk11_0,esk12_0,esk13_0) = k1_relat_1(esk13_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(esk13_0,esk11_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X64,X65,X66] :
      ( ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
      | m1_subset_1(k2_relset_1(X64,X65,X66),k1_zfmisc_1(X65)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_34,plain,(
    ! [X70,X71,X72] :
      ( ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
      | k2_relset_1(X70,X71,X72) = k2_relat_1(X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_35,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ v4_relat_1(X35,X34)
      | X35 = k7_relat_1(X35,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_36,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X9] : k3_xboole_0(X9,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_38,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_39,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k3_xboole_0(X7,X8) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_funct_2(k1_relat_1(X1),X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])])).

cnf(c_0_41,negated_conjecture,
    ( k1_relat_1(esk13_0) = esk11_0
    | esk12_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_30]),c_0_31])])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk13_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_25])).

fof(c_0_44,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_45,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_47,plain,(
    ! [X36] :
      ( ( k1_relat_1(X36) != k1_xboole_0
        | k2_relat_1(X36) = k1_xboole_0
        | ~ v1_relat_1(X36) )
      & ( k2_relat_1(X36) != k1_xboole_0
        | k1_relat_1(X36) = k1_xboole_0
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

fof(c_0_48,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | k2_relat_1(k7_relat_1(X33,X32)) = k9_relat_1(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_49,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( v4_relat_1(esk13_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_25])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | r2_hidden(esk13_0,k1_funct_2(esk11_0,X1))
    | ~ r1_tarski(k2_relat_1(esk13_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_57,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | k7_relat_1(X38,X37) = k3_xboole_0(X38,k2_zfmisc_1(X37,k2_relat_1(X38))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t96_relat_1])])).

cnf(c_0_58,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( k7_relat_1(esk13_0,esk11_0) = esk13_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_43])])).

fof(c_0_61,plain,(
    ! [X21,X22] :
      ( ( k2_zfmisc_1(X21,X22) != k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k2_zfmisc_1(X21,X22) = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k2_zfmisc_1(X21,X22) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | r2_hidden(esk13_0,k1_funct_2(esk11_0,X1))
    | ~ m1_subset_1(k2_relat_1(esk13_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk13_0),k1_zfmisc_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_25])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(esk13_0,k1_funct_2(esk11_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_67,plain,
    ( k7_relat_1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | k1_relat_1(k7_relat_1(X1,X2)) != k1_xboole_0
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( k9_relat_1(esk13_0,esk11_0) = k2_relat_1(esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_43])])).

cnf(c_0_70,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( esk12_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_74,plain,
    ( k7_relat_1(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_67,c_0_52])).

cnf(c_0_75,negated_conjecture,
    ( k2_relat_1(esk13_0) = k1_xboole_0
    | k1_relat_1(esk13_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_60]),c_0_69]),c_0_43])])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_xboole_0
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_59])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_55])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk13_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( k7_relat_1(esk13_0,X1) = k1_xboole_0
    | k1_relat_1(esk13_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_62]),c_0_43])])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(esk13_0) = k1_xboole_0
    | k2_relat_1(esk13_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_60]),c_0_69]),c_0_43])])).

cnf(c_0_82,negated_conjecture,
    ( k2_relat_1(esk13_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

fof(c_0_83,plain,(
    ! [X61,X62,X63] :
      ( ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
      | m1_subset_1(k1_relset_1(X61,X62,X63),k1_zfmisc_1(X61)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_84,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_85,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | esk12_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_86,negated_conjecture,
    ( esk13_0 = k1_xboole_0
    | k1_relat_1(esk13_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k1_relat_1(esk13_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_88,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_89,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( esk11_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_73])])).

cnf(c_0_91,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_92,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_93,negated_conjecture,
    ( esk13_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_94,plain,
    ( k1_relset_1(X1,k1_xboole_0,X2) = k1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_76])).

cnf(c_0_95,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_88]),c_0_89])).

cnf(c_0_96,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( ~ r2_hidden(esk13_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_73]),c_0_90])).

cnf(c_0_98,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_91]),c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_93])).

cnf(c_0_101,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_94]),c_0_76])])).

cnf(c_0_102,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_97,c_0_93])).

cnf(c_0_104,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X1))
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_99])]),c_0_100])])).

cnf(c_0_105,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_73]),c_0_76]),c_0_93])).

cnf(c_0_107,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_55]),c_0_108])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:28:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.031 s
% 0.21/0.42  # Presaturation interreduction done
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(t11_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 0.21/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.42  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.21/0.42  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.42  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.42  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.21/0.42  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.42  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.21/0.42  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.21/0.42  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.42  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.42  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.21/0.42  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.21/0.42  fof(t96_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k3_xboole_0(X2,k2_zfmisc_1(X1,k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 0.21/0.42  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.42  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.21/0.42  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.21/0.42  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2))))), inference(assume_negation,[status(cth)],[t11_funct_2])).
% 0.21/0.42  fof(c_0_20, plain, ![X67, X68, X69]:(~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))|k1_relset_1(X67,X68,X69)=k1_relat_1(X69)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.42  fof(c_0_21, negated_conjecture, (((v1_funct_1(esk13_0)&v1_funct_2(esk13_0,esk11_0,esk12_0))&m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0))))&((esk12_0!=k1_xboole_0|esk11_0=k1_xboole_0)&~r2_hidden(esk13_0,k1_funct_2(esk11_0,esk12_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.21/0.42  fof(c_0_22, plain, ![X83, X84, X85, X86, X88, X89, X90, X91, X92, X94]:(((((((v1_relat_1(esk8_4(X83,X84,X85,X86))|~r2_hidden(X86,X85)|X85!=k1_funct_2(X83,X84))&(v1_funct_1(esk8_4(X83,X84,X85,X86))|~r2_hidden(X86,X85)|X85!=k1_funct_2(X83,X84)))&(X86=esk8_4(X83,X84,X85,X86)|~r2_hidden(X86,X85)|X85!=k1_funct_2(X83,X84)))&(k1_relat_1(esk8_4(X83,X84,X85,X86))=X83|~r2_hidden(X86,X85)|X85!=k1_funct_2(X83,X84)))&(r1_tarski(k2_relat_1(esk8_4(X83,X84,X85,X86)),X84)|~r2_hidden(X86,X85)|X85!=k1_funct_2(X83,X84)))&(~v1_relat_1(X89)|~v1_funct_1(X89)|X88!=X89|k1_relat_1(X89)!=X83|~r1_tarski(k2_relat_1(X89),X84)|r2_hidden(X88,X85)|X85!=k1_funct_2(X83,X84)))&((~r2_hidden(esk9_3(X90,X91,X92),X92)|(~v1_relat_1(X94)|~v1_funct_1(X94)|esk9_3(X90,X91,X92)!=X94|k1_relat_1(X94)!=X90|~r1_tarski(k2_relat_1(X94),X91))|X92=k1_funct_2(X90,X91))&(((((v1_relat_1(esk10_3(X90,X91,X92))|r2_hidden(esk9_3(X90,X91,X92),X92)|X92=k1_funct_2(X90,X91))&(v1_funct_1(esk10_3(X90,X91,X92))|r2_hidden(esk9_3(X90,X91,X92),X92)|X92=k1_funct_2(X90,X91)))&(esk9_3(X90,X91,X92)=esk10_3(X90,X91,X92)|r2_hidden(esk9_3(X90,X91,X92),X92)|X92=k1_funct_2(X90,X91)))&(k1_relat_1(esk10_3(X90,X91,X92))=X90|r2_hidden(esk9_3(X90,X91,X92),X92)|X92=k1_funct_2(X90,X91)))&(r1_tarski(k2_relat_1(esk10_3(X90,X91,X92)),X91)|r2_hidden(esk9_3(X90,X91,X92),X92)|X92=k1_funct_2(X90,X91))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.21/0.42  fof(c_0_23, plain, ![X80, X81, X82]:((((~v1_funct_2(X82,X80,X81)|X80=k1_relset_1(X80,X81,X82)|X81=k1_xboole_0|~m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))))&(X80!=k1_relset_1(X80,X81,X82)|v1_funct_2(X82,X80,X81)|X81=k1_xboole_0|~m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81)))))&((~v1_funct_2(X82,X80,X81)|X80=k1_relset_1(X80,X81,X82)|X80!=k1_xboole_0|~m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))))&(X80!=k1_relset_1(X80,X81,X82)|v1_funct_2(X82,X80,X81)|X80!=k1_xboole_0|~m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))))))&((~v1_funct_2(X82,X80,X81)|X82=k1_xboole_0|X80=k1_xboole_0|X81!=k1_xboole_0|~m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))))&(X82!=k1_xboole_0|v1_funct_2(X82,X80,X81)|X80=k1_xboole_0|X81!=k1_xboole_0|~m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.42  cnf(c_0_24, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.42  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  fof(c_0_26, plain, ![X55, X56, X57]:(~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))|v1_relat_1(X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.42  fof(c_0_27, plain, ![X58, X59, X60]:((v4_relat_1(X60,X58)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59))))&(v5_relat_1(X60,X59)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.42  cnf(c_0_28, plain, (r2_hidden(X2,X5)|~v1_relat_1(X1)|~v1_funct_1(X1)|X2!=X1|k1_relat_1(X1)!=X3|~r1_tarski(k2_relat_1(X1),X4)|X5!=k1_funct_2(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.42  cnf(c_0_29, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.42  cnf(c_0_30, negated_conjecture, (k1_relset_1(esk11_0,esk12_0,esk13_0)=k1_relat_1(esk13_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.42  cnf(c_0_31, negated_conjecture, (v1_funct_2(esk13_0,esk11_0,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_32, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.42  fof(c_0_33, plain, ![X64, X65, X66]:(~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))|m1_subset_1(k2_relset_1(X64,X65,X66),k1_zfmisc_1(X65))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.21/0.42  fof(c_0_34, plain, ![X70, X71, X72]:(~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))|k2_relset_1(X70,X71,X72)=k2_relat_1(X72)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.42  fof(c_0_35, plain, ![X34, X35]:(~v1_relat_1(X35)|~v4_relat_1(X35,X34)|X35=k7_relat_1(X35,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.21/0.42  cnf(c_0_36, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.42  fof(c_0_37, plain, ![X9]:k3_xboole_0(X9,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.21/0.42  fof(c_0_38, plain, ![X10, X11]:k4_xboole_0(X10,k4_xboole_0(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.42  fof(c_0_39, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k3_xboole_0(X7,X8)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.42  cnf(c_0_40, plain, (r2_hidden(X1,k1_funct_2(k1_relat_1(X1),X2))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(er,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])])).
% 0.21/0.42  cnf(c_0_41, negated_conjecture, (k1_relat_1(esk13_0)=esk11_0|esk12_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_25]), c_0_30]), c_0_31])])).
% 0.21/0.42  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk13_0)), inference(spm,[status(thm)],[c_0_32, c_0_25])).
% 0.21/0.42  fof(c_0_44, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.42  cnf(c_0_45, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.42  cnf(c_0_46, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.42  fof(c_0_47, plain, ![X36]:((k1_relat_1(X36)!=k1_xboole_0|k2_relat_1(X36)=k1_xboole_0|~v1_relat_1(X36))&(k2_relat_1(X36)!=k1_xboole_0|k1_relat_1(X36)=k1_xboole_0|~v1_relat_1(X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.21/0.42  fof(c_0_48, plain, ![X32, X33]:(~v1_relat_1(X33)|k2_relat_1(k7_relat_1(X33,X32))=k9_relat_1(X33,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.21/0.42  cnf(c_0_49, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.42  cnf(c_0_50, negated_conjecture, (v4_relat_1(esk13_0,esk11_0)), inference(spm,[status(thm)],[c_0_36, c_0_25])).
% 0.21/0.42  cnf(c_0_51, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.42  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.42  cnf(c_0_53, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.42  cnf(c_0_54, negated_conjecture, (esk12_0=k1_xboole_0|r2_hidden(esk13_0,k1_funct_2(esk11_0,X1))|~r1_tarski(k2_relat_1(esk13_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])])).
% 0.21/0.42  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.42  cnf(c_0_56, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.42  fof(c_0_57, plain, ![X37, X38]:(~v1_relat_1(X38)|k7_relat_1(X38,X37)=k3_xboole_0(X38,k2_zfmisc_1(X37,k2_relat_1(X38)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t96_relat_1])])).
% 0.21/0.42  cnf(c_0_58, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.42  cnf(c_0_59, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.42  cnf(c_0_60, negated_conjecture, (k7_relat_1(esk13_0,esk11_0)=esk13_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_43])])).
% 0.21/0.42  fof(c_0_61, plain, ![X21, X22]:((k2_zfmisc_1(X21,X22)!=k1_xboole_0|(X21=k1_xboole_0|X22=k1_xboole_0))&((X21!=k1_xboole_0|k2_zfmisc_1(X21,X22)=k1_xboole_0)&(X22!=k1_xboole_0|k2_zfmisc_1(X21,X22)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.42  cnf(c_0_62, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.42  cnf(c_0_63, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_52])).
% 0.21/0.42  cnf(c_0_64, negated_conjecture, (esk12_0=k1_xboole_0|r2_hidden(esk13_0,k1_funct_2(esk11_0,X1))|~m1_subset_1(k2_relat_1(esk13_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.42  cnf(c_0_65, negated_conjecture, (m1_subset_1(k2_relat_1(esk13_0),k1_zfmisc_1(esk12_0))), inference(spm,[status(thm)],[c_0_56, c_0_25])).
% 0.21/0.42  cnf(c_0_66, negated_conjecture, (~r2_hidden(esk13_0,k1_funct_2(esk11_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_67, plain, (k7_relat_1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.42  cnf(c_0_68, plain, (k9_relat_1(X1,X2)=k1_xboole_0|k1_relat_1(k7_relat_1(X1,X2))!=k1_xboole_0|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.42  cnf(c_0_69, negated_conjecture, (k9_relat_1(esk13_0,esk11_0)=k2_relat_1(esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_43])])).
% 0.21/0.42  cnf(c_0_70, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.42  cnf(c_0_71, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.42  cnf(c_0_72, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.42  cnf(c_0_73, negated_conjecture, (esk12_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.21/0.42  cnf(c_0_74, plain, (k7_relat_1(X1,X2)=k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(X1))))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_67, c_0_52])).
% 0.21/0.42  cnf(c_0_75, negated_conjecture, (k2_relat_1(esk13_0)=k1_xboole_0|k1_relat_1(esk13_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_60]), c_0_69]), c_0_43])])).
% 0.21/0.42  cnf(c_0_76, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_70])).
% 0.21/0.42  cnf(c_0_77, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_xboole_0|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_59])).
% 0.21/0.42  cnf(c_0_78, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_72, c_0_55])).
% 0.21/0.42  cnf(c_0_79, negated_conjecture, (m1_subset_1(k2_relat_1(esk13_0),k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_65, c_0_73])).
% 0.21/0.42  cnf(c_0_80, negated_conjecture, (k7_relat_1(esk13_0,X1)=k1_xboole_0|k1_relat_1(esk13_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_62]), c_0_43])])).
% 0.21/0.42  cnf(c_0_81, negated_conjecture, (k1_relat_1(esk13_0)=k1_xboole_0|k2_relat_1(esk13_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_60]), c_0_69]), c_0_43])])).
% 0.21/0.42  cnf(c_0_82, negated_conjecture, (k2_relat_1(esk13_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.21/0.42  fof(c_0_83, plain, ![X61, X62, X63]:(~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))|m1_subset_1(k1_relset_1(X61,X62,X63),k1_zfmisc_1(X61))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.21/0.42  cnf(c_0_84, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.42  cnf(c_0_85, negated_conjecture, (esk11_0=k1_xboole_0|esk12_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_86, negated_conjecture, (esk13_0=k1_xboole_0|k1_relat_1(esk13_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_80])).
% 0.21/0.42  cnf(c_0_87, negated_conjecture, (k1_relat_1(esk13_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.21/0.42  cnf(c_0_88, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.21/0.42  cnf(c_0_89, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_84])).
% 0.21/0.42  cnf(c_0_90, negated_conjecture, (esk11_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_73])])).
% 0.21/0.42  cnf(c_0_91, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.21/0.42  cnf(c_0_92, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.21/0.42  cnf(c_0_93, negated_conjecture, (esk13_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 0.21/0.42  cnf(c_0_94, plain, (k1_relset_1(X1,k1_xboole_0,X2)=k1_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_24, c_0_76])).
% 0.21/0.42  cnf(c_0_95, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_88]), c_0_89])).
% 0.21/0.42  cnf(c_0_96, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_24, c_0_89])).
% 0.21/0.42  cnf(c_0_97, negated_conjecture, (~r2_hidden(esk13_0,k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_73]), c_0_90])).
% 0.21/0.42  cnf(c_0_98, plain, (r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X1))|~v1_funct_1(k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_91]), c_0_92])).
% 0.21/0.42  cnf(c_0_99, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_42, c_0_93])).
% 0.21/0.42  cnf(c_0_100, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_43, c_0_93])).
% 0.21/0.42  cnf(c_0_101, plain, (m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_94]), c_0_76])])).
% 0.21/0.42  cnf(c_0_102, plain, (k1_relat_1(X1)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.21/0.42  cnf(c_0_103, negated_conjecture, (~r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[c_0_97, c_0_93])).
% 0.21/0.42  cnf(c_0_104, plain, (r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X1))|~r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_99])]), c_0_100])])).
% 0.21/0.42  cnf(c_0_105, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.21/0.42  cnf(c_0_106, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_73]), c_0_76]), c_0_93])).
% 0.21/0.42  cnf(c_0_107, negated_conjecture, (~r1_tarski(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.21/0.42  cnf(c_0_108, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.21/0.42  cnf(c_0_109, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_55]), c_0_108])]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 110
% 0.21/0.42  # Proof object clause steps            : 72
% 0.21/0.42  # Proof object formula steps           : 38
% 0.21/0.42  # Proof object conjectures             : 35
% 0.21/0.42  # Proof object clause conjectures      : 32
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 26
% 0.21/0.42  # Proof object initial formulas used   : 19
% 0.21/0.42  # Proof object generating inferences   : 30
% 0.21/0.42  # Proof object simplifying inferences  : 54
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 30
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 74
% 0.21/0.42  # Removed in clause preprocessing      : 2
% 0.21/0.42  # Initial clauses in saturation        : 72
% 0.21/0.42  # Processed clauses                    : 466
% 0.21/0.42  # ...of these trivial                  : 14
% 0.21/0.42  # ...subsumed                          : 141
% 0.21/0.42  # ...remaining for further processing  : 311
% 0.21/0.42  # Other redundant clauses eliminated   : 18
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 13
% 0.21/0.42  # Backward-rewritten                   : 85
% 0.21/0.42  # Generated clauses                    : 667
% 0.21/0.42  # ...of the previous two non-trivial   : 673
% 0.21/0.42  # Contextual simplify-reflections      : 13
% 0.21/0.42  # Paramodulations                      : 652
% 0.21/0.42  # Factorizations                       : 0
% 0.21/0.42  # Equation resolutions                 : 18
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 127
% 0.21/0.42  #    Positive orientable unit clauses  : 19
% 0.21/0.42  #    Positive unorientable unit clauses: 0
% 0.21/0.42  #    Negative unit clauses             : 3
% 0.21/0.42  #    Non-unit-clauses                  : 105
% 0.21/0.42  # Current number of unprocessed clauses: 324
% 0.21/0.42  # ...number of literals in the above   : 2398
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 171
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 7477
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 2411
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 166
% 0.21/0.42  # Unit Clause-clause subsumption calls : 207
% 0.21/0.42  # Rewrite failures with RHS unbound    : 0
% 0.21/0.42  # BW rewrite match attempts            : 17
% 0.21/0.42  # BW rewrite match successes           : 15
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 31920
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.074 s
% 0.21/0.43  # System time              : 0.007 s
% 0.21/0.43  # Total time               : 0.081 s
% 0.21/0.43  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
