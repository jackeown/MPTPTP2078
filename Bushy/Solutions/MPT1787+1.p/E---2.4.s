%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t102_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:02 EDT 2019

% Result     : Theorem 212.73s
% Output     : CNFRefutation 212.73s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 224 expanded)
%              Number of clauses        :   49 (  91 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  325 ( 954 expanded)
%              Number of equality atoms :   45 (  66 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t102_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r2_hidden(X2,k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t102_tmap_1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',d1_pre_topc)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t2_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',commutativity_k3_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',redefinition_k9_subset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',existence_m1_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t3_subset)).

fof(fraenkel_a_2_0_tmap_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_0_tmap_1(X2,X3))
      <=> ? [X4,X5] :
            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
            & X1 = k4_subset_1(u1_struct_0(X2),X4,k9_subset_1(u1_struct_0(X2),X5,X3))
            & r2_hidden(X4,u1_pre_topc(X2))
            & r2_hidden(X5,u1_pre_topc(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',fraenkel_a_2_0_tmap_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t4_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',dt_u1_pre_topc)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',dt_k9_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t28_xboole_1)).

fof(d8_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k5_tmap_1(X1,X2) = a_2_0_tmap_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',d8_tmap_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',redefinition_k4_subset_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',commutativity_k2_xboole_0)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',commutativity_k9_subset_1)).

fof(t5_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t5_pre_topc)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => r2_hidden(X2,k5_tmap_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t102_tmap_1])).

fof(c_0_19,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r1_tarski(X21,u1_pre_topc(X20))
        | r2_hidden(k5_setfam_1(u1_struct_0(X20),X21),u1_pre_topc(X20))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(X22,u1_pre_topc(X20))
        | ~ r2_hidden(X23,u1_pre_topc(X20))
        | r2_hidden(k9_subset_1(u1_struct_0(X20),X22,X23),u1_pre_topc(X20))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk5_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk4_1(X20),u1_pre_topc(X20))
        | m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk5_1(X20),u1_pre_topc(X20))
        | m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X20),esk4_1(X20),esk5_1(X20)),u1_pre_topc(X20))
        | m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | r1_tarski(esk3_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk5_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | r1_tarski(esk3_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk4_1(X20),u1_pre_topc(X20))
        | r1_tarski(esk3_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk5_1(X20),u1_pre_topc(X20))
        | r1_tarski(esk3_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X20),esk4_1(X20),esk5_1(X20)),u1_pre_topc(X20))
        | r1_tarski(esk3_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk5_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk4_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk5_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X20),esk4_1(X20),esk5_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r2_hidden(esk2_0,k5_tmap_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_21,plain,(
    ! [X80] : k3_xboole_0(X80,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_22,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_23,plain,(
    ! [X70,X71,X72] :
      ( ~ m1_subset_1(X72,k1_zfmisc_1(X70))
      | k9_subset_1(X70,X71,X72) = k3_xboole_0(X71,X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_24,plain,(
    ! [X48] : m1_subset_1(esk9_1(X48),X48) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_25,plain,(
    ! [X87,X88] :
      ( ( ~ m1_subset_1(X87,k1_zfmisc_1(X88))
        | r1_tarski(X87,X88) )
      & ( ~ r1_tarski(X87,X88)
        | m1_subset_1(X87,k1_zfmisc_1(X88)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_26,plain,(
    ! [X50,X51,X52,X55,X56] :
      ( ( m1_subset_1(esk10_3(X50,X51,X52),k1_zfmisc_1(u1_struct_0(X51)))
        | ~ r2_hidden(X50,a_2_0_tmap_1(X51,X52))
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51))) )
      & ( m1_subset_1(esk11_3(X50,X51,X52),k1_zfmisc_1(u1_struct_0(X51)))
        | ~ r2_hidden(X50,a_2_0_tmap_1(X51,X52))
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51))) )
      & ( X50 = k4_subset_1(u1_struct_0(X51),esk10_3(X50,X51,X52),k9_subset_1(u1_struct_0(X51),esk11_3(X50,X51,X52),X52))
        | ~ r2_hidden(X50,a_2_0_tmap_1(X51,X52))
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51))) )
      & ( r2_hidden(esk10_3(X50,X51,X52),u1_pre_topc(X51))
        | ~ r2_hidden(X50,a_2_0_tmap_1(X51,X52))
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51))) )
      & ( r2_hidden(esk11_3(X50,X51,X52),u1_pre_topc(X51))
        | ~ r2_hidden(X50,a_2_0_tmap_1(X51,X52))
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51))) )
      & ( ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X51)))
        | X50 != k4_subset_1(u1_struct_0(X51),X55,k9_subset_1(u1_struct_0(X51),X56,X52))
        | ~ r2_hidden(X55,u1_pre_topc(X51))
        | ~ r2_hidden(X56,u1_pre_topc(X51))
        | r2_hidden(X50,a_2_0_tmap_1(X51,X52))
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_tmap_1])])])])])])).

fof(c_0_27,plain,(
    ! [X89,X90,X91] :
      ( ~ r2_hidden(X89,X90)
      | ~ m1_subset_1(X90,k1_zfmisc_1(X91))
      | m1_subset_1(X89,X91) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_28,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_31,plain,(
    ! [X43] :
      ( ~ l1_pre_topc(X43)
      | m1_subset_1(u1_pre_topc(X43),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X43)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_32,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X37))
      | m1_subset_1(k9_subset_1(X37,X38,X39),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk9_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_37,plain,(
    ! [X78,X79] :
      ( ~ r1_tarski(X78,X79)
      | k3_xboole_0(X78,X79) = X78 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_40,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | k5_tmap_1(X27,X28) = a_2_0_tmap_1(X27,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tmap_1])])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X4,a_2_0_tmap_1(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k4_subset_1(u1_struct_0(X2),X1,k9_subset_1(u1_struct_0(X2),X3,X5))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_44,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_45,plain,(
    ! [X65,X66,X67] :
      ( ~ m1_subset_1(X66,k1_zfmisc_1(X65))
      | ~ m1_subset_1(X67,k1_zfmisc_1(X65))
      | k4_subset_1(X65,X66,X67) = k2_xboole_0(X66,X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_46,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_48,plain,
    ( k9_subset_1(X1,X2,esk9_1(k1_zfmisc_1(X1))) = k3_xboole_0(X2,esk9_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_49,plain,(
    ! [X73] : k2_xboole_0(X73,k1_xboole_0) = X73 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_50,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(X1,esk2_0) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_39])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | k5_tmap_1(X1,X2) = a_2_0_tmap_1(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X3,X4)),a_2_0_tmap_1(X1,X4))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),X1)
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

cnf(c_0_59,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_39])).

cnf(c_0_61,plain,
    ( k9_subset_1(X1,k1_xboole_0,esk9_1(k1_zfmisc_1(X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_64,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k9_subset_1(X17,X18,X19) = k9_subset_1(X17,X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_65,negated_conjecture,
    ( k3_xboole_0(esk2_0,u1_struct_0(esk1_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(esk2_0,X1) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_53])).

fof(c_0_67,plain,(
    ! [X92] :
      ( ~ v2_pre_topc(X92)
      | ~ l1_pre_topc(X92)
      | r2_hidden(k1_xboole_0,u1_pre_topc(X92)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_pre_topc])])).

cnf(c_0_68,negated_conjecture,
    ( k5_tmap_1(esk1_0,X1) = a_2_0_tmap_1(esk1_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_29]),c_0_30])]),c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k4_subset_1(u1_struct_0(esk1_0),X1,k9_subset_1(u1_struct_0(esk1_0),X2,X3)),a_2_0_tmap_1(esk1_0,X3))
    | ~ r2_hidden(X2,u1_pre_topc(esk1_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk1_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_29]),c_0_30])]),c_0_55])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_71,negated_conjecture,
    ( k2_xboole_0(X1,k9_subset_1(u1_struct_0(esk1_0),X2,esk2_0)) = k4_subset_1(u1_struct_0(esk1_0),X1,k9_subset_1(u1_struct_0(esk1_0),X2,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_72,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_61]),c_0_36])])).

cnf(c_0_73,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_74,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k5_tmap_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_78,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = a_2_0_tmap_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_39])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k4_subset_1(u1_struct_0(esk1_0),X1,k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),X2)),a_2_0_tmap_1(esk1_0,X2))
    | ~ r2_hidden(X1,u1_pre_topc(esk1_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_43]),c_0_70])])).

cnf(c_0_80,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k1_xboole_0,k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_39])).

cnf(c_0_82,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,u1_struct_0(esk1_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_70])])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_29]),c_0_30])])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(esk2_0,a_2_0_tmap_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82]),c_0_83]),c_0_39]),c_0_72])]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
