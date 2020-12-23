%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t173_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:36 EDT 2019

% Result     : Theorem 152.19s
% Output     : CNFRefutation 152.25s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 731 expanded)
%              Number of clauses        :   76 ( 276 expanded)
%              Number of leaves         :   21 ( 180 expanded)
%              Depth                    :   13
%              Number of atoms          :  415 (5785 expanded)
%              Number of equality atoms :   62 ( 778 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t173_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X4,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,X1)
                           => ( r2_hidden(X6,X4)
                             => k3_funct_2(X1,X2,X3,X6) = k1_funct_1(X5,X6) ) )
                       => k2_partfun1(X1,X2,X3,X4) = X5 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t173_funct_2)).

fof(existence_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ? [X3] : m2_subset_1(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',existence_m2_subset_1)).

fof(rc1_subset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
          & ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',rc1_subset_1)).

fof(t38_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
            & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
            & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t38_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t3_subset)).

fof(dt_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ! [X3] :
          ( m2_subset_1(X3,X1,X2)
         => m1_subset_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',dt_m2_subset_1)).

fof(t113_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t113_funct_2)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',dt_k2_partfun1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t2_subset)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',redefinition_k3_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',existence_m1_subset_1)).

fof(dt_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => m1_subset_1(k3_funct_2(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',dt_k3_funct_2)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t72_funct_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',redefinition_k2_partfun1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',cc1_relset_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',d2_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',t6_boole)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t173_funct_2.p',redefinition_r2_relset_1)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ! [X4] :
                    ( ( ~ v1_xboole_0(X4)
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,X4,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                       => ( ! [X6] :
                              ( m1_subset_1(X6,X1)
                             => ( r2_hidden(X6,X4)
                               => k3_funct_2(X1,X2,X3,X6) = k1_funct_1(X5,X6) ) )
                         => k2_partfun1(X1,X2,X3,X4) = X5 ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t173_funct_2])).

fof(c_0_22,plain,(
    ! [X30,X31] :
      ( v1_xboole_0(X30)
      | v1_xboole_0(X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | m2_subset_1(esk7_2(X30,X31),X30,X31) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_subset_1])])])])).

fof(c_0_23,plain,(
    ! [X88] :
      ( ( m1_subset_1(esk9_1(X88),k1_zfmisc_1(X88))
        | v1_xboole_0(X88) )
      & ( ~ v1_xboole_0(esk9_1(X88))
        | v1_xboole_0(X88) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).

fof(c_0_24,plain,(
    ! [X65,X66,X67,X68] :
      ( ( v1_funct_1(k2_partfun1(X65,X66,X68,X67))
        | X66 = k1_xboole_0
        | ~ r1_tarski(X67,X65)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X65,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( v1_funct_2(k2_partfun1(X65,X66,X68,X67),X67,X66)
        | X66 = k1_xboole_0
        | ~ r1_tarski(X67,X65)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X65,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( m1_subset_1(k2_partfun1(X65,X66,X68,X67),k1_zfmisc_1(k2_zfmisc_1(X67,X66)))
        | X66 = k1_xboole_0
        | ~ r1_tarski(X67,X65)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X65,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( v1_funct_1(k2_partfun1(X65,X66,X68,X67))
        | X65 != k1_xboole_0
        | ~ r1_tarski(X67,X65)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X65,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( v1_funct_2(k2_partfun1(X65,X66,X68,X67),X67,X66)
        | X65 != k1_xboole_0
        | ~ r1_tarski(X67,X65)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X65,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( m1_subset_1(k2_partfun1(X65,X66,X68,X67),k1_zfmisc_1(k2_zfmisc_1(X67,X66)))
        | X65 != k1_xboole_0
        | ~ r1_tarski(X67,X65)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X65,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_funct_2])])])).

fof(c_0_25,negated_conjecture,(
    ! [X12] :
      ( ~ v1_xboole_0(esk1_0)
      & ~ v1_xboole_0(esk2_0)
      & v1_funct_1(esk3_0)
      & v1_funct_2(esk3_0,esk1_0,esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & ~ v1_xboole_0(esk4_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk4_0,esk2_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))
      & ( ~ m1_subset_1(X12,esk1_0)
        | ~ r2_hidden(X12,esk4_0)
        | k3_funct_2(esk1_0,esk2_0,esk3_0,X12) = k1_funct_1(esk5_0,X12) )
      & k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0) != esk5_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])])).

fof(c_0_26,plain,(
    ! [X69,X70] :
      ( ( ~ m1_subset_1(X69,k1_zfmisc_1(X70))
        | r1_tarski(X69,X70) )
      & ( ~ r1_tarski(X69,X70)
        | m1_subset_1(X69,k1_zfmisc_1(X70)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_27,plain,(
    ! [X25,X26,X27] :
      ( v1_xboole_0(X25)
      | v1_xboole_0(X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | ~ m2_subset_1(X27,X25,X26)
      | m1_subset_1(X27,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_subset_1])])])])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m2_subset_1(esk7_2(X1,X2),X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk9_1(X1),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(esk9_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X56,X57,X58,X59] :
      ( ( m1_subset_1(esk8_4(X56,X57,X58,X59),X56)
        | r2_relset_1(X56,X57,X58,X59)
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X56,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( k1_funct_1(X58,esk8_4(X56,X57,X58,X59)) != k1_funct_1(X59,esk8_4(X56,X57,X58,X59))
        | r2_relset_1(X56,X57,X58,X59)
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X56,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_funct_2])])])])])).

cnf(c_0_32,plain,
    ( v1_funct_2(k2_partfun1(X1,X2,X3,X4),X4,X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X4,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_38,plain,(
    ! [X15,X16,X17,X18] :
      ( ( v1_funct_1(k2_partfun1(X15,X16,X17,X18))
        | ~ v1_funct_1(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( m1_subset_1(k2_partfun1(X15,X16,X17,X18),k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | X2 = k1_xboole_0
    | ~ r1_tarski(X4,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_40,plain,(
    ! [X71,X72,X73] :
      ( ~ r2_hidden(X71,X72)
      | ~ m1_subset_1(X72,k1_zfmisc_1(X73))
      | m1_subset_1(X71,X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_41,plain,(
    ! [X63,X64] :
      ( ~ m1_subset_1(X63,X64)
      | v1_xboole_0(X64)
      | r2_hidden(X63,X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m2_subset_1(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( m2_subset_1(esk7_2(X1,esk9_1(X1)),X1,esk9_1(X1))
    | v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk8_4(X1,X2,X3,X4),X1)
    | r2_relset_1(X1,X2,X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_50,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( m1_subset_1(esk7_2(X1,esk9_1(X1)),X1)
    | v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_29]),c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( r2_relset_1(esk4_0,esk2_0,X1,esk5_0)
    | m1_subset_1(esk8_4(esk4_0,esk2_0,X1,esk5_0),esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))
    | ~ v1_funct_2(X1,esk4_0,esk2_0)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_56,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_34]),c_0_35])])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_49])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,esk9_1(X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_29])).

cnf(c_0_60,plain,
    ( r2_hidden(esk7_2(X1,esk9_1(X1)),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_61,plain,(
    ! [X37,X38,X39,X40] :
      ( v1_xboole_0(X37)
      | ~ v1_funct_1(X39)
      | ~ v1_funct_2(X39,X37,X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | ~ m1_subset_1(X40,X37)
      | k3_funct_2(X37,X38,X39,X40) = k1_funct_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_62,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
    | m1_subset_1(esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])]),c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_64,plain,(
    ! [X74,X75,X76] :
      ( ~ r2_hidden(X74,X75)
      | ~ m1_subset_1(X75,k1_zfmisc_1(X76))
      | ~ v1_xboole_0(X76) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_65,plain,(
    ! [X28] : m1_subset_1(esk6_1(X28),X28) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_66,plain,(
    ! [X19,X20,X21,X22] :
      ( v1_xboole_0(X19)
      | ~ v1_funct_1(X21)
      | ~ v1_funct_2(X21,X19,X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | ~ m1_subset_1(X22,X19)
      | m1_subset_1(k3_funct_2(X19,X20,X21,X22),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_funct_2])])])).

cnf(c_0_67,plain,
    ( m1_subset_1(esk7_2(esk9_1(X1),esk9_1(esk9_1(X1))),X1)
    | v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_30])).

fof(c_0_68,plain,(
    ! [X78,X79,X80] :
      ( ~ v1_relat_1(X80)
      | ~ v1_funct_1(X80)
      | ~ r2_hidden(X78,X79)
      | k1_funct_1(k7_relat_1(X80,X79),X78) = k1_funct_1(X80,X78) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

fof(c_0_69,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ v1_funct_1(X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k2_partfun1(X33,X34,X35,X36) = k7_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_70,plain,(
    ! [X85,X86,X87] :
      ( ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86)))
      | v1_relat_1(X87) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(X1,esk1_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_37])).

cnf(c_0_74,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
    | r2_hidden(esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_62]),c_0_63])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k3_funct_2(X1,X3,X2,X4),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_78,plain,
    ( r2_hidden(esk7_2(esk9_1(X1),esk9_1(esk9_1(X1))),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_67])).

cnf(c_0_79,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_80,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_82,negated_conjecture,
    ( k3_funct_2(esk1_0,esk2_0,esk3_0,X1) = k1_funct_1(esk3_0,X1)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_33]),c_0_34]),c_0_35])]),c_0_72])).

cnf(c_0_83,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
    | m1_subset_1(esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( k3_funct_2(esk1_0,esk2_0,esk3_0,X1) = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,esk6_1(k1_zfmisc_1(X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_86,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_76])).

cnf(c_0_87,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_88,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k3_funct_2(esk1_0,esk2_0,esk3_0,X1),esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_33]),c_0_34]),c_0_35])]),c_0_72])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk7_2(esk9_1(esk4_0),esk9_1(esk9_1(esk4_0))),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_78]),c_0_63])).

cnf(c_0_91,negated_conjecture,
    ( k1_funct_1(k7_relat_1(X1,esk4_0),esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)) = k1_funct_1(X1,esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0))
    | esk2_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_74])).

cnf(c_0_92,negated_conjecture,
    ( k7_relat_1(esk3_0,X1) = k2_partfun1(esk1_0,esk2_0,esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_34]),c_0_35])])).

cnf(c_0_93,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_34])).

cnf(c_0_94,negated_conjecture,
    ( k3_funct_2(esk1_0,esk2_0,esk3_0,esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)) = k1_funct_1(esk3_0,esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0))
    | esk2_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_95,negated_conjecture,
    ( k3_funct_2(esk1_0,esk2_0,esk3_0,esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)) = k1_funct_1(esk5_0,esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0))
    | esk2_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_83]),c_0_74])).

fof(c_0_96,plain,(
    ! [X77] :
      ( ~ v1_xboole_0(X77)
      | X77 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_97,plain,
    ( v1_xboole_0(esk6_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_98,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(k3_funct_2(esk1_0,esk2_0,esk3_0,esk7_2(esk9_1(esk4_0),esk9_1(esk9_1(esk4_0)))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_101,plain,(
    ! [X44,X45,X46,X47] :
      ( ( ~ r2_relset_1(X44,X45,X46,X47)
        | X46 = X47
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X46 != X47
        | r2_relset_1(X44,X45,X46,X47)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_102,plain,
    ( r2_relset_1(X2,X3,X1,X4)
    | k1_funct_1(X1,esk8_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk8_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_103,negated_conjecture,
    ( k1_funct_1(k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)) = k1_funct_1(esk3_0,esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0))
    | esk2_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_35]),c_0_92]),c_0_93])])).

cnf(c_0_104,negated_conjecture,
    ( k1_funct_1(esk5_0,esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)) = k1_funct_1(esk3_0,esk8_4(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0))
    | esk2_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_105,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_106,plain,
    ( v1_xboole_0(esk6_1(k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk1_0,esk2_0,esk3_0,esk7_2(esk9_1(esk4_0),esk9_1(esk9_1(esk4_0)))),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_99]),c_0_100])).

cnf(c_0_108,negated_conjecture,
    ( k3_funct_2(esk1_0,esk2_0,esk3_0,esk7_2(esk9_1(esk4_0),esk9_1(esk9_1(esk4_0)))) = k1_funct_1(esk3_0,esk7_2(esk9_1(esk4_0),esk9_1(esk9_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_90])).

cnf(c_0_109,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_110,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk2_0,k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_46]),c_0_45]),c_0_47]),c_0_57])]),c_0_56]),c_0_58]),c_0_104])).

cnf(c_0_111,negated_conjecture,
    ( k2_partfun1(esk1_0,esk2_0,esk3_0,esk4_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_112,plain,
    ( esk6_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk7_2(esk9_1(esk4_0),esk9_1(esk9_1(esk4_0)))),esk2_0) ),
    inference(rw,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_46])]),c_0_111]),c_0_58])).

cnf(c_0_115,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_112]),c_0_98])])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114]),c_0_115]),
    [proof]).
%------------------------------------------------------------------------------
