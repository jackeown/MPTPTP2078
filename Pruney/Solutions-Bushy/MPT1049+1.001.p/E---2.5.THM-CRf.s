%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1049+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:39 EST 2020

% Result     : Theorem 12.54s
% Output     : CNFRefutation 12.54s
% Verified   : 
% Statistics : Number of formulae       :  145 (2417 expanded)
%              Number of clauses        :  103 ( 970 expanded)
%              Number of leaves         :   21 ( 596 expanded)
%              Depth                    :   22
%              Number of atoms          :  585 (12442 expanded)
%              Number of equality atoms :   90 (1296 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( X4 = k5_partfun1(X1,X2,X3)
        <=> ! [X5] :
              ( r2_hidden(X5,X4)
            <=> ? [X6] :
                  ( v1_funct_1(X6)
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & X6 = X5
                  & v1_partfun1(X6,X1)
                  & r1_partfun1(X3,X6) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(t166_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( r1_tarski(k1_relset_1(X1,X2,X4),k1_relset_1(X1,X2,X3))
              & r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,X4)) )
           => r1_relset_1(X1,X2,X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_2)).

fof(t148_funct_2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t8_grfunc_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( r1_tarski(X1,X2)
          <=> ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_grfunc_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t171_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_relat_1(X4)
            & v1_funct_1(X4) )
         => ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
           => r1_partfun1(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_partfun1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t158_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ( ( r1_partfun1(X3,X5)
                  & r1_partfun1(X4,X5)
                  & v1_partfun1(X5,X1) )
               => r1_partfun1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_partfun1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(d6_partfun1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
          <=> ! [X3] :
                ( r2_hidden(X3,k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))
               => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_partfun1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(redefinition_r1_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_relset_1(X1,X2,X3,X4)
      <=> r1_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_relset_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(c_0_21,plain,(
    ! [X31,X32,X33,X34,X35,X37,X38,X39,X41] :
      ( ( v1_funct_1(esk3_5(X31,X32,X33,X34,X35))
        | ~ r2_hidden(X35,X34)
        | X34 != k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( m1_subset_1(esk3_5(X31,X32,X33,X34,X35),k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | ~ r2_hidden(X35,X34)
        | X34 != k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( esk3_5(X31,X32,X33,X34,X35) = X35
        | ~ r2_hidden(X35,X34)
        | X34 != k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v1_partfun1(esk3_5(X31,X32,X33,X34,X35),X31)
        | ~ r2_hidden(X35,X34)
        | X34 != k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( r1_partfun1(X33,esk3_5(X31,X32,X33,X34,X35))
        | ~ r2_hidden(X35,X34)
        | X34 != k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( ~ v1_funct_1(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | X38 != X37
        | ~ v1_partfun1(X38,X31)
        | ~ r1_partfun1(X33,X38)
        | r2_hidden(X37,X34)
        | X34 != k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( ~ r2_hidden(esk4_4(X31,X32,X33,X39),X39)
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | X41 != esk4_4(X31,X32,X33,X39)
        | ~ v1_partfun1(X41,X31)
        | ~ r1_partfun1(X33,X41)
        | X39 = k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v1_funct_1(esk5_4(X31,X32,X33,X39))
        | r2_hidden(esk4_4(X31,X32,X33,X39),X39)
        | X39 = k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( m1_subset_1(esk5_4(X31,X32,X33,X39),k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | r2_hidden(esk4_4(X31,X32,X33,X39),X39)
        | X39 = k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( esk5_4(X31,X32,X33,X39) = esk4_4(X31,X32,X33,X39)
        | r2_hidden(esk4_4(X31,X32,X33,X39),X39)
        | X39 = k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v1_partfun1(esk5_4(X31,X32,X33,X39),X31)
        | r2_hidden(esk4_4(X31,X32,X33,X39),X39)
        | X39 = k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( r1_partfun1(X33,esk5_4(X31,X32,X33,X39))
        | r2_hidden(esk4_4(X31,X32,X33,X39),X39)
        | X39 = k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( ( r1_tarski(k1_relset_1(X1,X2,X4),k1_relset_1(X1,X2,X3))
                & r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,X4)) )
             => r1_relset_1(X1,X2,X4,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t166_funct_2])).

cnf(c_0_23,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X63,X64,X65] :
      ( ( v1_funct_1(esk7_3(X63,X64,X65))
        | X64 = k1_xboole_0
        | ~ v1_funct_1(X65)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( v1_funct_2(esk7_3(X63,X64,X65),X63,X64)
        | X64 = k1_xboole_0
        | ~ v1_funct_1(X65)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( m1_subset_1(esk7_3(X63,X64,X65),k1_zfmisc_1(k2_zfmisc_1(X63,X64)))
        | X64 = k1_xboole_0
        | ~ v1_funct_1(X65)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( r1_partfun1(X65,esk7_3(X63,X64,X65))
        | X64 = k1_xboole_0
        | ~ v1_funct_1(X65)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( v1_funct_1(esk7_3(X63,X64,X65))
        | X63 != k1_xboole_0
        | ~ v1_funct_1(X65)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( v1_funct_2(esk7_3(X63,X64,X65),X63,X64)
        | X63 != k1_xboole_0
        | ~ v1_funct_1(X65)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( m1_subset_1(esk7_3(X63,X64,X65),k1_zfmisc_1(k2_zfmisc_1(X63,X64)))
        | X63 != k1_xboole_0
        | ~ v1_funct_1(X65)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( r1_partfun1(X65,esk7_3(X63,X64,X65))
        | X63 != k1_xboole_0
        | ~ v1_funct_1(X65)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t148_funct_2])])])])])).

fof(c_0_25,negated_conjecture,
    ( v1_funct_1(esk11_0)
    & m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))
    & v1_funct_1(esk12_0)
    & m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))
    & r1_tarski(k1_relset_1(esk9_0,esk10_0,esk12_0),k1_relset_1(esk9_0,esk10_0,esk11_0))
    & r1_tarski(k5_partfun1(esk9_0,esk10_0,esk11_0),k5_partfun1(esk9_0,esk10_0,esk12_0))
    & ~ r1_relset_1(esk9_0,esk10_0,esk12_0,esk11_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_26,plain,(
    ! [X79,X80] :
      ( ( ~ m1_subset_1(X79,k1_zfmisc_1(X80))
        | r1_tarski(X79,X80) )
      & ( ~ r1_tarski(X79,X80)
        | m1_subset_1(X79,k1_zfmisc_1(X80)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_partfun1(X3,X4,X5)
    | ~ r1_partfun1(X5,X1)
    | ~ v1_partfun1(X1,X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X13,X14,X15] :
      ( ( v1_funct_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | v1_xboole_0(X14) )
      & ( v1_partfun1(X15,X13)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | v1_xboole_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( v1_funct_1(esk7_3(X1,X2,X3))
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v1_funct_2(esk7_3(X1,X2,X3),X1,X2)
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X87] :
      ( ~ v1_xboole_0(X87)
      | X87 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_35,plain,(
    ! [X81,X82,X83] :
      ( ~ r2_hidden(X81,X82)
      | ~ m1_subset_1(X82,k1_zfmisc_1(X83))
      | m1_subset_1(X81,X83) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk9_0,esk10_0,esk11_0),k5_partfun1(esk9_0,esk10_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( r1_partfun1(X1,esk7_3(X2,X3,X1))
    | X3 = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | m1_subset_1(esk7_3(esk9_0,esk10_0,esk11_0),k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_42,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | v1_funct_1(esk7_3(esk9_0,esk10_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_31])])).

cnf(c_0_43,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | v1_funct_2(esk7_3(esk9_0,esk10_0,esk11_0),esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_31])])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_45,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k1_relset_1(X51,X52,X53) = k1_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k5_partfun1(esk9_0,esk10_0,esk11_0),k1_zfmisc_1(k5_partfun1(esk9_0,esk10_0,esk12_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk9_0,esk10_0,esk11_0))
    | ~ r1_partfun1(esk11_0,X1)
    | ~ v1_partfun1(X1,esk9_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_31])])).

cnf(c_0_49,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_partfun1(esk11_0,esk7_3(esk9_0,esk10_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_30]),c_0_31])])).

cnf(c_0_50,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | v1_partfun1(esk7_3(esk9_0,esk10_0,esk11_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k1_relset_1(esk9_0,esk10_0,esk12_0),k1_relset_1(esk9_0,esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_52,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_54,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_55,plain,(
    ! [X77,X78] :
      ( ~ m1_subset_1(X77,X78)
      | v1_xboole_0(X78)
      | r2_hidden(X77,X78) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(X1,k5_partfun1(esk9_0,esk10_0,esk12_0))
    | ~ r2_hidden(X1,k5_partfun1(esk9_0,esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r2_hidden(esk7_3(esk9_0,esk10_0,esk11_0),k5_partfun1(esk9_0,esk10_0,esk11_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_41]),c_0_42]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k1_relset_1(esk9_0,esk10_0,esk12_0),k1_zfmisc_1(k1_relset_1(esk9_0,esk10_0,esk11_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_51])).

fof(c_0_59,plain,(
    ! [X88,X89,X90] :
      ( ( r1_tarski(k1_relat_1(X88),k1_relat_1(X89))
        | ~ r1_tarski(X88,X89)
        | ~ v1_relat_1(X89)
        | ~ v1_funct_1(X89)
        | ~ v1_relat_1(X88)
        | ~ v1_funct_1(X88) )
      & ( ~ r2_hidden(X90,k1_relat_1(X88))
        | k1_funct_1(X88,X90) = k1_funct_1(X89,X90)
        | ~ r1_tarski(X88,X89)
        | ~ v1_relat_1(X89)
        | ~ v1_funct_1(X89)
        | ~ v1_relat_1(X88)
        | ~ v1_funct_1(X88) )
      & ( r2_hidden(esk8_2(X88,X89),k1_relat_1(X88))
        | ~ r1_tarski(k1_relat_1(X88),k1_relat_1(X89))
        | r1_tarski(X88,X89)
        | ~ v1_relat_1(X89)
        | ~ v1_funct_1(X89)
        | ~ v1_relat_1(X88)
        | ~ v1_funct_1(X88) )
      & ( k1_funct_1(X88,esk8_2(X88,X89)) != k1_funct_1(X89,esk8_2(X88,X89))
        | ~ r1_tarski(k1_relat_1(X88),k1_relat_1(X89))
        | r1_tarski(X88,X89)
        | ~ v1_relat_1(X89)
        | ~ v1_funct_1(X89)
        | ~ v1_relat_1(X88)
        | ~ v1_funct_1(X88) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_grfunc_1])])])])])).

cnf(c_0_60,negated_conjecture,
    ( k1_relset_1(esk9_0,esk10_0,esk12_0) = k1_relat_1(esk12_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k1_relset_1(esk9_0,esk10_0,esk11_0) = k1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_30])).

cnf(c_0_62,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_63,plain,(
    ! [X84,X85,X86] :
      ( ~ r2_hidden(X84,X85)
      | ~ m1_subset_1(X85,k1_zfmisc_1(X86))
      | ~ v1_xboole_0(X86) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_64,plain,(
    ! [X72,X73,X74,X75] :
      ( ~ v1_funct_1(X74)
      | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))
      | ~ v1_relat_1(X75)
      | ~ v1_funct_1(X75)
      | ~ r2_hidden(X75,k5_partfun1(X72,X73,X74))
      | r1_partfun1(X74,X75) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_partfun1])])])).

cnf(c_0_65,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | m1_subset_1(esk7_3(esk9_0,esk10_0,esk11_0),k5_partfun1(esk9_0,esk10_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_67,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( r2_hidden(X21,X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | ~ r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk1_3(X23,X24,X25),X25)
        | ~ r2_hidden(esk1_3(X23,X24,X25),X23)
        | ~ r2_hidden(esk1_3(X23,X24,X25),X24)
        | X25 = k3_xboole_0(X23,X24) )
      & ( r2_hidden(esk1_3(X23,X24,X25),X23)
        | r2_hidden(esk1_3(X23,X24,X25),X25)
        | X25 = k3_xboole_0(X23,X24) )
      & ( r2_hidden(esk1_3(X23,X24,X25),X24)
        | r2_hidden(esk1_3(X23,X24,X25),X25)
        | X25 = k3_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(X1,k1_relset_1(esk9_0,esk10_0,esk11_0))
    | ~ r2_hidden(X1,k1_relset_1(esk9_0,esk10_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_58])).

cnf(c_0_69,plain,
    ( r2_hidden(esk8_2(X1,X2),k1_relat_1(X1))
    | r1_tarski(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk12_0),k1_relat_1(esk11_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_60]),c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_72,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_30])).

cnf(c_0_73,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_53])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4)
    | ~ r2_hidden(X4,k5_partfun1(X2,X3,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r2_hidden(esk7_3(esk9_0,esk10_0,esk11_0),k5_partfun1(esk9_0,esk10_0,esk12_0))
    | v1_xboole_0(k5_partfun1(esk9_0,esk10_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | v1_relat_1(esk7_3(esk9_0,esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_41])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(X1,k1_relat_1(esk11_0))
    | ~ r2_hidden(X1,k1_relat_1(esk12_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_60]),c_0_61])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk12_0,esk11_0)
    | r2_hidden(esk8_2(esk12_0,esk11_0),k1_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_31]),c_0_71]),c_0_72]),c_0_73])])).

fof(c_0_81,plain,(
    ! [X67,X68,X69,X70,X71] :
      ( ~ v1_funct_1(X69)
      | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
      | ~ v1_funct_1(X70)
      | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
      | ~ v1_funct_1(X71)
      | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
      | ~ r1_partfun1(X69,X71)
      | ~ r1_partfun1(X70,X71)
      | ~ v1_partfun1(X71,X67)
      | r1_partfun1(X69,X70) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_partfun1])])])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(X1,k5_partfun1(esk9_0,esk10_0,esk11_0))
    | ~ v1_xboole_0(k5_partfun1(esk9_0,esk10_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_47])).

cnf(c_0_83,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_partfun1(esk12_0,esk7_3(esk9_0,esk10_0,esk11_0))
    | v1_xboole_0(k5_partfun1(esk9_0,esk10_0,esk12_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_71]),c_0_53])]),c_0_77]),c_0_42])).

fof(c_0_84,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_xboole_0(X10)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X10)))
      | v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_85,plain,(
    ! [X49] : m1_subset_1(esk6_1(X49),X49) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk12_0,esk11_0)
    | m1_subset_1(esk8_2(esk12_0,esk11_0),k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_partfun1(X1,X5)
    | ~ r1_partfun1(X4,X5)
    | ~ v1_partfun1(X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_partfun1(esk12_0,esk7_3(esk9_0,esk10_0,esk11_0))
    | ~ r2_hidden(X1,k5_partfun1(esk9_0,esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_91,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_92,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r1_partfun1(X27,X28)
        | ~ r2_hidden(X29,k3_xboole_0(k1_relat_1(X27),k1_relat_1(X28)))
        | k1_funct_1(X27,X29) = k1_funct_1(X28,X29)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( r2_hidden(esk2_2(X27,X28),k3_xboole_0(k1_relat_1(X27),k1_relat_1(X28)))
        | r1_partfun1(X27,X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( k1_funct_1(X27,esk2_2(X27,X28)) != k1_funct_1(X28,esk2_2(X27,X28))
        | r1_partfun1(X27,X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_partfun1])])])])])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk12_0,esk11_0)
    | r2_hidden(esk8_2(esk12_0,esk11_0),k3_xboole_0(X1,k1_relat_1(esk12_0)))
    | ~ r2_hidden(esk8_2(esk12_0,esk11_0),X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_80])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(esk12_0,esk11_0)
    | r2_hidden(esk8_2(esk12_0,esk11_0),k1_relat_1(esk11_0))
    | v1_xboole_0(k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_87])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,X2)
    | k1_funct_1(X1,esk8_2(X1,X2)) != k1_funct_1(X2,esk8_2(X1,X2))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_96,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_partfun1(X1,X2)
    | ~ r1_partfun1(X2,esk7_3(esk9_0,esk10_0,esk11_0))
    | ~ r1_partfun1(X1,esk7_3(esk9_0,esk10_0,esk11_0))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_41]),c_0_42]),c_0_50])).

cnf(c_0_97,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_partfun1(esk12_0,esk7_3(esk9_0,esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_57])).

cnf(c_0_98,plain,
    ( v1_xboole_0(esk6_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_99,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_100,plain,
    ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
    | ~ r1_partfun1(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(esk12_0,esk11_0)
    | r2_hidden(esk8_2(esk12_0,esk11_0),k3_xboole_0(k1_relat_1(esk11_0),k1_relat_1(esk12_0)))
    | v1_xboole_0(k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk12_0,esk11_0)
    | k1_funct_1(esk12_0,esk8_2(esk12_0,esk11_0)) != k1_funct_1(esk11_0,esk8_2(esk12_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_70]),c_0_31]),c_0_71]),c_0_72]),c_0_73])])).

cnf(c_0_103,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_partfun1(X1,esk12_0)
    | ~ r1_partfun1(X1,esk7_3(esk9_0,esk10_0,esk11_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_53]),c_0_71])]),c_0_97])).

cnf(c_0_104,plain,
    ( esk6_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_98])).

cnf(c_0_105,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_99])).

fof(c_0_106,plain,(
    ! [X57,X58,X59,X60] :
      ( ( ~ r1_relset_1(X57,X58,X59,X60)
        | r1_tarski(X59,X60)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( ~ r1_tarski(X59,X60)
        | r1_relset_1(X57,X58,X59,X60)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_relset_1])])])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(esk12_0,esk11_0)
    | v1_xboole_0(k1_relat_1(esk11_0))
    | ~ r1_partfun1(esk11_0,esk12_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_71]),c_0_31]),c_0_73]),c_0_72])]),c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_partfun1(esk11_0,esk12_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_30]),c_0_31])]),c_0_49])).

fof(c_0_109,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | m1_subset_1(k1_relset_1(X43,X44,X45),k1_zfmisc_1(X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_110,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_91,c_0_104])).

cnf(c_0_111,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_99,c_0_105])).

cnf(c_0_112,plain,
    ( r1_relset_1(X3,X4,X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_113,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_tarski(esk12_0,esk11_0)
    | v1_xboole_0(k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_114,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_115,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relset_1(esk9_0,esk10_0,esk12_0))
    | ~ v1_xboole_0(k1_relset_1(esk9_0,esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_58])).

cnf(c_0_117,negated_conjecture,
    ( r1_relset_1(esk9_0,esk10_0,esk12_0,X1)
    | ~ r1_tarski(esk12_0,X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_53])).

cnf(c_0_118,negated_conjecture,
    ( k1_relat_1(esk11_0) = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | r1_tarski(esk12_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( ~ r1_relset_1(esk9_0,esk10_0,esk12_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_120,plain,
    ( m1_subset_1(k1_relset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_121,plain,
    ( k1_relset_1(X1,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_115])).

cnf(c_0_122,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk12_0))
    | ~ v1_xboole_0(k1_relat_1(esk11_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_60]),c_0_61])).

cnf(c_0_123,negated_conjecture,
    ( k1_relat_1(esk11_0) = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119])).

cnf(c_0_124,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_125,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | ~ r2_hidden(X1,k1_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_111])])).

cnf(c_0_126,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_124])).

cnf(c_0_127,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_128,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_tarski(esk12_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_80])).

cnf(c_0_129,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_126])).

cnf(c_0_130,plain,
    ( r1_tarski(k1_relset_1(X1,k1_xboole_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_127,c_0_120])).

cnf(c_0_131,negated_conjecture,
    ( v1_xboole_0(esk11_0)
    | ~ v1_xboole_0(esk10_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_30])).

cnf(c_0_132,negated_conjecture,
    ( esk10_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_128]),c_0_119])).

cnf(c_0_133,negated_conjecture,
    ( v1_xboole_0(esk12_0)
    | ~ v1_xboole_0(esk10_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_53])).

cnf(c_0_134,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_129,c_0_111])).

cnf(c_0_135,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[c_0_130,c_0_121])).

cnf(c_0_136,negated_conjecture,
    ( v1_xboole_0(esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_132]),c_0_111])])).

cnf(c_0_137,negated_conjecture,
    ( v1_xboole_0(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_132]),c_0_111])])).

cnf(c_0_138,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_124,c_0_134])).

cnf(c_0_139,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[c_0_135,c_0_134])).

cnf(c_0_140,negated_conjecture,
    ( ~ r1_relset_1(esk9_0,k1_xboole_0,esk12_0,esk11_0) ),
    inference(rw,[status(thm)],[c_0_119,c_0_132])).

cnf(c_0_141,negated_conjecture,
    ( esk11_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_136])).

cnf(c_0_142,negated_conjecture,
    ( esk12_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_137])).

cnf(c_0_143,plain,
    ( r1_relset_1(X1,X2,k1_xboole_0,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_138]),c_0_139])])).

cnf(c_0_144,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_141]),c_0_142]),c_0_143])]),
    [proof]).

%------------------------------------------------------------------------------
