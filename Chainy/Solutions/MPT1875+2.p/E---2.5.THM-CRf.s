%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1875+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:09 EST 2020

% Result     : Theorem 15.51s
% Output     : CNFRefutation 15.51s
% Verified   : 
% Statistics : Number of formulae       :   29 (  56 expanded)
%              Number of clauses        :   16 (  21 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   90 ( 207 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',d4_subset_1)).

fof(t43_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(t27_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( X2 = u1_struct_0(X1)
           => ( v2_tex_2(X2,X1)
            <=> v1_tdlat_3(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

fof(t28_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r1_tarski(X3,X2)
                  & v2_tex_2(X2,X1) )
               => v2_tex_2(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t3_subset)).

fof(c_0_6,plain,(
    ! [X1583] : m1_subset_1(k2_subset_1(X1583),k1_zfmisc_1(X1583)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_7,plain,(
    ! [X1539] : k2_subset_1(X1539) = X1539 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v2_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t43_tex_2])).

fof(c_0_9,plain,(
    ! [X11815,X11816] :
      ( ( ~ v2_tex_2(X11816,X11815)
        | v1_tdlat_3(X11815)
        | X11816 != u1_struct_0(X11815)
        | ~ m1_subset_1(X11816,k1_zfmisc_1(u1_struct_0(X11815)))
        | v2_struct_0(X11815)
        | ~ l1_pre_topc(X11815) )
      & ( ~ v1_tdlat_3(X11815)
        | v2_tex_2(X11816,X11815)
        | X11816 != u1_struct_0(X11815)
        | ~ m1_subset_1(X11816,k1_zfmisc_1(u1_struct_0(X11815)))
        | v2_struct_0(X11815)
        | ~ l1_pre_topc(X11815) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_tex_2])])])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X11817,X11818,X11819] :
      ( ~ l1_pre_topc(X11817)
      | ~ m1_subset_1(X11818,k1_zfmisc_1(u1_struct_0(X11817)))
      | ~ m1_subset_1(X11819,k1_zfmisc_1(u1_struct_0(X11817)))
      | ~ r1_tarski(X11819,X11818)
      | ~ v2_tex_2(X11818,X11817)
      | v2_tex_2(X11819,X11817) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_tex_2])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1361_0)
    & v2_pre_topc(esk1361_0)
    & v1_tdlat_3(esk1361_0)
    & l1_pre_topc(esk1361_0)
    & m1_subset_1(esk1362_0,k1_zfmisc_1(u1_struct_0(esk1361_0)))
    & ~ v2_tex_2(esk1362_0,esk1361_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_14,plain,
    ( v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_16,plain,(
    ! [X2019,X2020] :
      ( ( ~ m1_subset_1(X2019,k1_zfmisc_1(X2020))
        | r1_tarski(X2019,X2020) )
      & ( ~ r1_tarski(X2019,X2020)
        | m1_subset_1(X2019,k1_zfmisc_1(X2020)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_17,plain,
    ( v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk1362_0,k1_zfmisc_1(u1_struct_0(esk1361_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1361_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_tex_2(esk1362_0,esk1361_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v2_tex_2(u1_struct_0(X1),X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])])).

cnf(c_0_22,negated_conjecture,
    ( v1_tdlat_3(esk1361_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1361_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_tex_2(X1,esk1361_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1361_0)))
    | ~ r1_tarski(esk1362_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk1361_0),esk1361_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_22])]),c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1362_0,u1_struct_0(esk1361_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_26]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
