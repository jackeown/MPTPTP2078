%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:26 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  157 (146287 expanded)
%              Number of clauses        :  130 (56425 expanded)
%              Number of leaves         :   13 (34564 expanded)
%              Depth                    :   37
%              Number of atoms          :  653 (1148455 expanded)
%              Number of equality atoms :  131 (167146 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(t63_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t62_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                   => ( X3 = X4
                     => ( v5_pre_topc(X3,X1,X2)
                      <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_pre_topc])).

fof(c_0_14,plain,(
    ! [X32,X33,X34,X35] :
      ( ( ~ v5_pre_topc(X34,X32,X33)
        | v5_pre_topc(X35,X32,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))
        | X34 != X35
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(X32),u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33))))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33))))))
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ v5_pre_topc(X35,X32,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))
        | v5_pre_topc(X34,X32,X33)
        | X34 != X35
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(X32),u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33))))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33))))))
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).

fof(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))
    & esk3_0 = esk4_0
    & ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
      | ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) )
    & ( v5_pre_topc(esk3_0,esk1_0,esk2_0)
      | v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_16,plain,
    ( v5_pre_topc(X4,X2,X3)
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | X4 != X1
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_22,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v1_funct_2(X23,X21,X22)
        | X21 = k1_relset_1(X21,X22,X23)
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X21 != k1_relset_1(X21,X22,X23)
        | v1_funct_2(X23,X21,X22)
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( ~ v1_funct_2(X23,X21,X22)
        | X21 = k1_relset_1(X21,X22,X23)
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X21 != k1_relset_1(X21,X22,X23)
        | v1_funct_2(X23,X21,X22)
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( ~ v1_funct_2(X23,X21,X22)
        | X23 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X23 != k1_xboole_0
        | v1_funct_2(X23,X21,X22)
        | X21 = k1_xboole_0
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_23,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_32,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k1_relset_1(X18,X19,X20) = k1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_33,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_37,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_18])).

fof(c_0_38,plain,(
    ! [X27] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_40,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_41,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = u1_struct_0(esk1_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_43,negated_conjecture,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),esk3_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_24]),c_0_28])])).

cnf(c_0_44,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_48,plain,(
    ! [X24,X25] :
      ( ( v1_pre_topc(g1_pre_topc(X24,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))) )
      & ( l1_pre_topc(g1_pre_topc(X24,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_31])).

fof(c_0_50,plain,(
    ! [X9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_52,plain,(
    ! [X28,X29,X30,X31] :
      ( ( ~ v5_pre_topc(X30,X28,X29)
        | v5_pre_topc(X31,g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)),X29)
        | X30 != X31
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28))),u1_struct_0(X29))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28))),u1_struct_0(X29))))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ v5_pre_topc(X31,g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)),X29)
        | v5_pre_topc(X30,X28,X29)
        | X30 != X31
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28))),u1_struct_0(X29))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28))),u1_struct_0(X29))))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_34])])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_43]),c_0_24])])).

cnf(c_0_55,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_56,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_57,plain,(
    ! [X26] :
      ( ~ l1_pre_topc(X26)
      | m1_subset_1(u1_pre_topc(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_58,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) = esk3_0
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_24])).

cnf(c_0_59,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_51])).

cnf(c_0_61,plain,
    ( v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v5_pre_topc(X1,X2,X3)
    | X1 != X4
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_62,plain,
    ( v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | X1 != X4
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = u1_struct_0(esk1_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = k1_xboole_0
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,plain,
    ( v5_pre_topc(X4,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | X4 != X1
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_67,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_51]),c_0_59])])).

cnf(c_0_69,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_60]),c_0_59])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_71,plain,
    ( v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_72,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = u1_struct_0(esk1_0)
    | m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_60])).

cnf(c_0_74,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_47])])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = u1_struct_0(esk1_0)
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_64]),c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_70,c_0_18])).

cnf(c_0_78,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_79,negated_conjecture,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X2)
    | m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(X1,esk1_0,X2)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_46]),c_0_47])])).

cnf(c_0_80,negated_conjecture,
    ( v5_pre_topc(X1,esk1_0,X2)
    | m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X2)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_73]),c_0_46]),c_0_47])])).

cnf(c_0_81,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_35]),c_0_34])])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_59])).

cnf(c_0_83,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_34]),c_0_25]),c_0_26]),c_0_27]),c_0_35])])).

cnf(c_0_85,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_25]),c_0_26]),c_0_27]),c_0_35]),c_0_34])]),c_0_82])).

fof(c_0_86,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | m1_subset_1(k1_relset_1(X15,X16,X17),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_87,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_76]),c_0_35]),c_0_34])])).

cnf(c_0_88,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_82])).

cnf(c_0_89,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_24]),c_0_25]),c_0_46]),c_0_47]),c_0_28])])).

cnf(c_0_91,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_92,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_85])).

cnf(c_0_93,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_41])).

cnf(c_0_94,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk1_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_97,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_98,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_59])).

cnf(c_0_99,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_91]),c_0_95])).

cnf(c_0_100,plain,
    ( v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | u1_struct_0(X2) != k1_xboole_0
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_91])).

cnf(c_0_101,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_56])).

cnf(c_0_102,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relat_1(X1) != X2
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_41])).

cnf(c_0_103,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_25]),c_0_26]),c_0_46]),c_0_27]),c_0_47]),c_0_35]),c_0_34])]),c_0_95])).

cnf(c_0_105,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_67]),c_0_47])])).

cnf(c_0_106,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | k1_xboole_0 != X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_59]),c_0_103])])).

cnf(c_0_107,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105]),c_0_105]),c_0_106])).

cnf(c_0_108,negated_conjecture,
    ( u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_51]),c_0_60])).

cnf(c_0_109,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | u1_struct_0(X3) != k1_xboole_0
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_51])).

cnf(c_0_110,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_111,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_45]),c_0_26]),c_0_27])])).

cnf(c_0_112,negated_conjecture,
    ( u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_25]),c_0_26]),c_0_46]),c_0_27]),c_0_47]),c_0_35]),c_0_34])]),c_0_60])).

cnf(c_0_113,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_110,c_0_59])).

cnf(c_0_114,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_111,c_0_56])).

cnf(c_0_115,negated_conjecture,
    ( u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_105]),c_0_105])).

cnf(c_0_116,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | u1_struct_0(esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_105]),c_0_103])).

cnf(c_0_117,plain,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_113]),c_0_106])).

cnf(c_0_118,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_67]),c_0_27])])).

cnf(c_0_119,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])]),c_0_118])).

cnf(c_0_120,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_121,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_120,c_0_56])).

cnf(c_0_122,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_67]),c_0_47])])).

cnf(c_0_123,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_105])).

cnf(c_0_124,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_105]),c_0_105]),c_0_105]),c_0_105]),c_0_59])])).

cnf(c_0_125,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_105]),c_0_105]),c_0_122])).

cnf(c_0_126,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_127,plain,
    ( v5_pre_topc(k1_xboole_0,X1,X2)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_59]),c_0_59])]),c_0_123])])).

cnf(c_0_128,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_125])])).

cnf(c_0_129,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_105])).

cnf(c_0_130,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_131,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_126])).

cnf(c_0_132,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_26]),c_0_46]),c_0_27]),c_0_47]),c_0_129])]),c_0_122])).

cnf(c_0_133,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_134,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_116]),c_0_117])])).

cnf(c_0_135,plain,
    ( m1_subset_1(k1_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_133])).

cnf(c_0_136,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) != k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_132,c_0_106])).

cnf(c_0_137,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_138,plain,
    ( v1_funct_2(k2_zfmisc_1(X1,X2),X1,X2)
    | k1_relat_1(k2_zfmisc_1(X1,X2)) != X1
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_133])).

cnf(c_0_139,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_135])).

cnf(c_0_140,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) != k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_141,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_137,c_0_56])).

cnf(c_0_142,plain,
    ( v1_funct_2(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_143,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) != k1_xboole_0
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_140,c_0_56])).

cnf(c_0_144,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_67]),c_0_47])])).

cnf(c_0_145,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_142,c_0_91])).

cnf(c_0_146,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_105]),c_0_103])).

cnf(c_0_147,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_67]),c_0_47])])).

cnf(c_0_148,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk1_0,X1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0))),u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_144]),c_0_46]),c_0_47])]),c_0_145])])).

cnf(c_0_149,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_125,c_0_144])).

cnf(c_0_150,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_151,plain,
    ( v5_pre_topc(X1,X2,X3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))) != k1_xboole_0
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_51])).

cnf(c_0_152,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_150]),c_0_117])])).

cnf(c_0_153,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_152]),c_0_150]),c_0_123]),c_0_26]),c_0_46]),c_0_27]),c_0_47]),c_0_144]),c_0_150]),c_0_117]),c_0_144]),c_0_145]),c_0_59]),c_0_59])]),c_0_122])).

cnf(c_0_154,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_45]),c_0_26]),c_0_27])])).

cnf(c_0_155,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_154,c_0_56])).

cnf(c_0_156,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_67]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:11:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.48  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.043 s
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t64_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_pre_topc)).
% 0.19/0.48  fof(t63_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.19/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.48  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.48  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.48  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.48  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.19/0.48  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.48  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.19/0.48  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.48  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.19/0.48  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.48  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.19/0.48  fof(c_0_13, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t64_pre_topc])).
% 0.19/0.48  fof(c_0_14, plain, ![X32, X33, X34, X35]:((~v5_pre_topc(X34,X32,X33)|v5_pre_topc(X35,X32,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))|X34!=X35|(~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X32),u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33))))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))))))|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33)))))|(~v2_pre_topc(X33)|~l1_pre_topc(X33))|(~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~v5_pre_topc(X35,X32,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))|v5_pre_topc(X34,X32,X33)|X34!=X35|(~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X32),u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33))))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))))))|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33)))))|(~v2_pre_topc(X33)|~l1_pre_topc(X33))|(~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).
% 0.19/0.48  fof(c_0_15, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))))&(esk3_0=esk4_0&((~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))&(v5_pre_topc(esk3_0,esk1_0,esk2_0)|v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.19/0.48  cnf(c_0_16, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.48  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_18, negated_conjecture, (esk3_0=esk4_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_19, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  fof(c_0_20, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.48  fof(c_0_21, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.48  fof(c_0_22, plain, ![X21, X22, X23]:((((~v1_funct_2(X23,X21,X22)|X21=k1_relset_1(X21,X22,X23)|X22=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X21!=k1_relset_1(X21,X22,X23)|v1_funct_2(X23,X21,X22)|X22=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))&((~v1_funct_2(X23,X21,X22)|X21=k1_relset_1(X21,X22,X23)|X21!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X21!=k1_relset_1(X21,X22,X23)|v1_funct_2(X23,X21,X22)|X21!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))))&((~v1_funct_2(X23,X21,X22)|X23=k1_xboole_0|X21=k1_xboole_0|X22!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X23!=k1_xboole_0|v1_funct_2(X23,X21,X22)|X21=k1_xboole_0|X22!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.48  cnf(c_0_23, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.48  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.19/0.48  cnf(c_0_29, negated_conjecture, (v5_pre_topc(esk3_0,esk1_0,esk2_0)|v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_30, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.48  fof(c_0_32, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|k1_relset_1(X18,X19,X20)=k1_relat_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.48  cnf(c_0_33, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.48  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_36, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])])).
% 0.19/0.48  cnf(c_0_37, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_29, c_0_18])).
% 0.19/0.48  fof(c_0_38, plain, ![X27]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.19/0.48  cnf(c_0_39, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.48  fof(c_0_40, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.48  cnf(c_0_41, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.48  cnf(c_0_42, negated_conjecture, (k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=u1_struct_0(esk1_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.19/0.48  cnf(c_0_43, negated_conjecture, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),esk3_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_24]), c_0_28])])).
% 0.19/0.48  cnf(c_0_44, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.48  cnf(c_0_45, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.48  cnf(c_0_46, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  fof(c_0_48, plain, ![X24, X25]:((v1_pre_topc(g1_pre_topc(X24,X25))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))))&(l1_pre_topc(g1_pre_topc(X24,X25))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.19/0.48  cnf(c_0_49, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_39, c_0_31])).
% 0.19/0.48  fof(c_0_50, plain, ![X9]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.48  cnf(c_0_51, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.48  fof(c_0_52, plain, ![X28, X29, X30, X31]:((~v5_pre_topc(X30,X28,X29)|v5_pre_topc(X31,g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)),X29)|X30!=X31|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28))),u1_struct_0(X29))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28))),u1_struct_0(X29)))))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29)))))|(~v2_pre_topc(X29)|~l1_pre_topc(X29))|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(~v5_pre_topc(X31,g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)),X29)|v5_pre_topc(X30,X28,X29)|X30!=X31|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28))),u1_struct_0(X29))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28))),u1_struct_0(X29)))))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29)))))|(~v2_pre_topc(X29)|~l1_pre_topc(X29))|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.19/0.48  cnf(c_0_53, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_34])])).
% 0.19/0.48  cnf(c_0_54, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_43]), c_0_24])])).
% 0.19/0.48  cnf(c_0_55, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])])).
% 0.19/0.48  cnf(c_0_56, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.48  fof(c_0_57, plain, ![X26]:(~l1_pre_topc(X26)|m1_subset_1(u1_pre_topc(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.48  cnf(c_0_58, negated_conjecture, (k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))=esk3_0|~m1_subset_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_24])).
% 0.19/0.48  cnf(c_0_59, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.48  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|u1_struct_0(esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_51])).
% 0.19/0.48  cnf(c_0_61, plain, (v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.48  cnf(c_0_62, plain, (v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.48  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_51])).
% 0.19/0.48  cnf(c_0_64, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))=u1_struct_0(esk1_0)|u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=k1_xboole_0|u1_struct_0(esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.48  cnf(c_0_65, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.48  cnf(c_0_66, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.48  cnf(c_0_67, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.48  cnf(c_0_68, negated_conjecture, (esk3_0=k1_xboole_0|u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_51]), c_0_59])])).
% 0.19/0.48  cnf(c_0_69, negated_conjecture, (esk3_0=k1_xboole_0|u1_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_60]), c_0_59])])).
% 0.19/0.48  cnf(c_0_70, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_71, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_61])).
% 0.19/0.48  cnf(c_0_72, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_62])).
% 0.19/0.48  cnf(c_0_73, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))=u1_struct_0(esk1_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_60])).
% 0.19/0.48  cnf(c_0_74, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_65])).
% 0.19/0.48  cnf(c_0_75, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_47])])).
% 0.19/0.48  cnf(c_0_76, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))=u1_struct_0(esk1_0)|esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_64]), c_0_69])).
% 0.19/0.48  cnf(c_0_77, negated_conjecture, (~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_70, c_0_18])).
% 0.19/0.48  cnf(c_0_78, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])])).
% 0.19/0.48  cnf(c_0_79, negated_conjecture, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X2)|m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~v5_pre_topc(X1,esk1_0,X2)|~v1_funct_1(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_46]), c_0_47])])).
% 0.19/0.48  cnf(c_0_80, negated_conjecture, (v5_pre_topc(X1,esk1_0,X2)|m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X2)|~v1_funct_1(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_73]), c_0_46]), c_0_47])])).
% 0.19/0.48  cnf(c_0_81, negated_conjecture, (esk3_0=k1_xboole_0|v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_35]), c_0_34])])).
% 0.19/0.48  cnf(c_0_82, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_49, c_0_59])).
% 0.19/0.48  cnf(c_0_83, negated_conjecture, (~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.48  cnf(c_0_84, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_34]), c_0_25]), c_0_26]), c_0_27]), c_0_35])])).
% 0.19/0.48  cnf(c_0_85, negated_conjecture, (esk3_0=k1_xboole_0|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_25]), c_0_26]), c_0_27]), c_0_35]), c_0_34])]), c_0_82])).
% 0.19/0.48  fof(c_0_86, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|m1_subset_1(k1_relset_1(X15,X16,X17),k1_zfmisc_1(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.19/0.48  cnf(c_0_87, negated_conjecture, (esk3_0=k1_xboole_0|~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_76]), c_0_35]), c_0_34])])).
% 0.19/0.48  cnf(c_0_88, negated_conjecture, (esk3_0=k1_xboole_0|v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_82])).
% 0.19/0.48  cnf(c_0_89, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.48  cnf(c_0_90, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_24]), c_0_25]), c_0_46]), c_0_47]), c_0_28])])).
% 0.19/0.48  cnf(c_0_91, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.48  cnf(c_0_92, negated_conjecture, (esk3_0=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_85])).
% 0.19/0.48  cnf(c_0_93, plain, (m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_89, c_0_41])).
% 0.19/0.48  cnf(c_0_94, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(spm,[status(thm)],[c_0_77, c_0_90])).
% 0.19/0.48  cnf(c_0_95, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|u1_struct_0(esk1_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_91])).
% 0.19/0.48  cnf(c_0_96, negated_conjecture, (esk3_0=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_45]), c_0_46]), c_0_47])])).
% 0.19/0.48  cnf(c_0_97, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.48  cnf(c_0_98, plain, (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_93, c_0_59])).
% 0.19/0.48  cnf(c_0_99, negated_conjecture, (u1_struct_0(esk1_0)!=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_91]), c_0_95])).
% 0.19/0.48  cnf(c_0_100, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|u1_struct_0(X2)!=k1_xboole_0|~v5_pre_topc(X1,X2,X3)|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_71, c_0_91])).
% 0.19/0.48  cnf(c_0_101, negated_conjecture, (esk3_0=k1_xboole_0|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_96, c_0_56])).
% 0.19/0.48  cnf(c_0_102, plain, (v1_funct_2(X1,X2,X3)|k1_relat_1(X1)!=X2|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_97, c_0_41])).
% 0.19/0.48  cnf(c_0_103, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_98])).
% 0.19/0.48  cnf(c_0_104, negated_conjecture, (u1_struct_0(esk1_0)!=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_25]), c_0_26]), c_0_46]), c_0_27]), c_0_47]), c_0_35]), c_0_34])]), c_0_95])).
% 0.19/0.48  cnf(c_0_105, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_67]), c_0_47])])).
% 0.19/0.48  cnf(c_0_106, plain, (v1_funct_2(k1_xboole_0,X1,X2)|k1_xboole_0!=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_59]), c_0_103])])).
% 0.19/0.48  cnf(c_0_107, negated_conjecture, (u1_struct_0(esk1_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105]), c_0_105]), c_0_106])).
% 0.19/0.48  cnf(c_0_108, negated_conjecture, (u1_struct_0(esk2_0)!=k1_xboole_0|~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_51]), c_0_60])).
% 0.19/0.48  cnf(c_0_109, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|u1_struct_0(X3)!=k1_xboole_0|~v5_pre_topc(X1,X2,X3)|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_72, c_0_51])).
% 0.19/0.48  cnf(c_0_110, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.48  cnf(c_0_111, negated_conjecture, (u1_struct_0(esk1_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_45]), c_0_26]), c_0_27])])).
% 0.19/0.48  cnf(c_0_112, negated_conjecture, (u1_struct_0(esk2_0)!=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_25]), c_0_26]), c_0_46]), c_0_27]), c_0_47]), c_0_35]), c_0_34])]), c_0_60])).
% 0.19/0.48  cnf(c_0_113, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_110, c_0_59])).
% 0.19/0.48  cnf(c_0_114, negated_conjecture, (u1_struct_0(esk1_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)|~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_111, c_0_56])).
% 0.19/0.48  cnf(c_0_115, negated_conjecture, (u1_struct_0(esk2_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_105]), c_0_105])).
% 0.19/0.48  cnf(c_0_116, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|u1_struct_0(esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_105]), c_0_103])).
% 0.19/0.48  cnf(c_0_117, plain, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_113]), c_0_106])).
% 0.19/0.48  cnf(c_0_118, negated_conjecture, (u1_struct_0(esk1_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_67]), c_0_27])])).
% 0.19/0.48  cnf(c_0_119, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117])]), c_0_118])).
% 0.19/0.48  cnf(c_0_120, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_45]), c_0_46]), c_0_47])])).
% 0.19/0.48  cnf(c_0_121, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_120, c_0_56])).
% 0.19/0.48  cnf(c_0_122, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_67]), c_0_47])])).
% 0.19/0.48  cnf(c_0_123, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_25, c_0_105])).
% 0.19/0.48  cnf(c_0_124, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_105]), c_0_105]), c_0_105]), c_0_105]), c_0_59])])).
% 0.19/0.48  cnf(c_0_125, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_105]), c_0_105]), c_0_122])).
% 0.19/0.48  cnf(c_0_126, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_127, plain, (v5_pre_topc(k1_xboole_0,X1,X2)|~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))|~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_59]), c_0_59])]), c_0_123])])).
% 0.19/0.48  cnf(c_0_128, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_125])])).
% 0.19/0.48  cnf(c_0_129, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_35, c_0_105])).
% 0.19/0.48  cnf(c_0_130, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.48  cnf(c_0_131, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_126])).
% 0.19/0.48  cnf(c_0_132, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_26]), c_0_46]), c_0_27]), c_0_47]), c_0_129])]), c_0_122])).
% 0.19/0.48  cnf(c_0_133, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 0.19/0.48  cnf(c_0_134, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_116]), c_0_117])])).
% 0.19/0.48  cnf(c_0_135, plain, (m1_subset_1(k1_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_93, c_0_133])).
% 0.19/0.48  cnf(c_0_136, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))!=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(spm,[status(thm)],[c_0_132, c_0_106])).
% 0.19/0.48  cnf(c_0_137, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_45]), c_0_46]), c_0_47])])).
% 0.19/0.48  cnf(c_0_138, plain, (v1_funct_2(k2_zfmisc_1(X1,X2),X1,X2)|k1_relat_1(k2_zfmisc_1(X1,X2))!=X1|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_102, c_0_133])).
% 0.19/0.48  cnf(c_0_139, plain, (k1_relat_1(k2_zfmisc_1(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_135])).
% 0.19/0.48  cnf(c_0_140, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))!=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_45]), c_0_46]), c_0_47])])).
% 0.19/0.48  cnf(c_0_141, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_137, c_0_56])).
% 0.19/0.48  cnf(c_0_142, plain, (v1_funct_2(k2_zfmisc_1(k1_xboole_0,X1),k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 0.19/0.48  cnf(c_0_143, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))!=k1_xboole_0|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_140, c_0_56])).
% 0.19/0.48  cnf(c_0_144, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_67]), c_0_47])])).
% 0.19/0.48  cnf(c_0_145, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_142, c_0_91])).
% 0.19/0.48  cnf(c_0_146, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=k1_xboole_0|u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_105]), c_0_103])).
% 0.19/0.48  cnf(c_0_147, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_67]), c_0_47])])).
% 0.19/0.48  cnf(c_0_148, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk1_0,X1)|~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0))),u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_144]), c_0_46]), c_0_47])]), c_0_145])])).
% 0.19/0.48  cnf(c_0_149, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(rw,[status(thm)],[c_0_125, c_0_144])).
% 0.19/0.48  cnf(c_0_150, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=k1_xboole_0), inference(sr,[status(thm)],[c_0_146, c_0_147])).
% 0.19/0.48  cnf(c_0_151, plain, (v5_pre_topc(X1,X2,X3)|u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))!=k1_xboole_0|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_23, c_0_51])).
% 0.19/0.48  cnf(c_0_152, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_150]), c_0_117])])).
% 0.19/0.48  cnf(c_0_153, negated_conjecture, (~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_152]), c_0_150]), c_0_123]), c_0_26]), c_0_46]), c_0_27]), c_0_47]), c_0_144]), c_0_150]), c_0_117]), c_0_144]), c_0_145]), c_0_59]), c_0_59])]), c_0_122])).
% 0.19/0.48  cnf(c_0_154, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_45]), c_0_26]), c_0_27])])).
% 0.19/0.48  cnf(c_0_155, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_154, c_0_56])).
% 0.19/0.48  cnf(c_0_156, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_67]), c_0_27])]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 157
% 0.19/0.48  # Proof object clause steps            : 130
% 0.19/0.48  # Proof object formula steps           : 27
% 0.19/0.48  # Proof object conjectures             : 89
% 0.19/0.48  # Proof object clause conjectures      : 86
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 31
% 0.19/0.48  # Proof object initial formulas used   : 13
% 0.19/0.48  # Proof object generating inferences   : 79
% 0.19/0.48  # Proof object simplifying inferences  : 185
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 14
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 40
% 0.19/0.48  # Removed in clause preprocessing      : 0
% 0.19/0.48  # Initial clauses in saturation        : 40
% 0.19/0.48  # Processed clauses                    : 615
% 0.19/0.48  # ...of these trivial                  : 21
% 0.19/0.48  # ...subsumed                          : 235
% 0.19/0.48  # ...remaining for further processing  : 359
% 0.19/0.48  # Other redundant clauses eliminated   : 14
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 50
% 0.19/0.48  # Backward-rewritten                   : 134
% 0.19/0.48  # Generated clauses                    : 2055
% 0.19/0.48  # ...of the previous two non-trivial   : 1821
% 0.19/0.48  # Contextual simplify-reflections      : 37
% 0.19/0.48  # Paramodulations                      : 1988
% 0.19/0.48  # Factorizations                       : 44
% 0.19/0.48  # Equation resolutions                 : 22
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 168
% 0.19/0.48  #    Positive orientable unit clauses  : 25
% 0.19/0.48  #    Positive unorientable unit clauses: 0
% 0.19/0.48  #    Negative unit clauses             : 6
% 0.19/0.48  #    Non-unit-clauses                  : 137
% 0.19/0.48  # Current number of unprocessed clauses: 927
% 0.19/0.48  # ...number of literals in the above   : 7197
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 185
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 23219
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 3844
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 300
% 0.19/0.48  # Unit Clause-clause subsumption calls : 243
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 68
% 0.19/0.48  # BW rewrite match successes           : 19
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 90338
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.143 s
% 0.19/0.48  # System time              : 0.005 s
% 0.19/0.48  # Total time               : 0.148 s
% 0.19/0.48  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
