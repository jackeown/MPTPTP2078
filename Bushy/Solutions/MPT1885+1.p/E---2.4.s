%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t53_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:53 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 ( 166 expanded)
%              Number of clauses        :   18 (  51 expanded)
%              Number of leaves         :    3 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :  131 (1400 expanded)
%              Number of equality atoms :   12 ( 124 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ ( v3_tex_2(X2,X1)
              & ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v1_pre_topc(X3)
                    & m1_pre_topc(X3,X1) )
                 => ~ ( v4_tex_2(X3,X1)
                      & X2 = u1_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t53_tex_2.p',t53_tex_2)).

fof(t10_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ? [X3] :
              ( ~ v2_struct_0(X3)
              & v1_pre_topc(X3)
              & m1_pre_topc(X3,X1)
              & X2 = u1_struct_0(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t53_tex_2.p',t10_tsep_1)).

fof(t51_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v3_tex_2(X3,X1)
                <=> v4_tex_2(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t53_tex_2.p',t51_tex_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ~ ( v3_tex_2(X2,X1)
                & ! [X3] :
                    ( ( ~ v2_struct_0(X3)
                      & v1_pre_topc(X3)
                      & m1_pre_topc(X3,X1) )
                   => ~ ( v4_tex_2(X3,X1)
                        & X2 = u1_struct_0(X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_tex_2])).

fof(c_0_4,plain,(
    ! [X326,X327] :
      ( ( ~ v2_struct_0(esk85_2(X326,X327))
        | v1_xboole_0(X327)
        | ~ m1_subset_1(X327,k1_zfmisc_1(u1_struct_0(X326)))
        | v2_struct_0(X326)
        | ~ l1_pre_topc(X326) )
      & ( v1_pre_topc(esk85_2(X326,X327))
        | v1_xboole_0(X327)
        | ~ m1_subset_1(X327,k1_zfmisc_1(u1_struct_0(X326)))
        | v2_struct_0(X326)
        | ~ l1_pre_topc(X326) )
      & ( m1_pre_topc(esk85_2(X326,X327),X326)
        | v1_xboole_0(X327)
        | ~ m1_subset_1(X327,k1_zfmisc_1(u1_struct_0(X326)))
        | v2_struct_0(X326)
        | ~ l1_pre_topc(X326) )
      & ( X327 = u1_struct_0(esk85_2(X326,X327))
        | v1_xboole_0(X327)
        | ~ m1_subset_1(X327,k1_zfmisc_1(u1_struct_0(X326)))
        | v2_struct_0(X326)
        | ~ l1_pre_topc(X326) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X7] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & ~ v1_xboole_0(esk2_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & v3_tex_2(esk2_0,esk1_0)
      & ( v2_struct_0(X7)
        | ~ v1_pre_topc(X7)
        | ~ m1_pre_topc(X7,esk1_0)
        | ~ v4_tex_2(X7,esk1_0)
        | esk2_0 != u1_struct_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])).

fof(c_0_6,plain,(
    ! [X338,X339,X340] :
      ( ( ~ v3_tex_2(X340,X338)
        | v4_tex_2(X339,X338)
        | X340 != u1_struct_0(X339)
        | ~ m1_subset_1(X340,k1_zfmisc_1(u1_struct_0(X338)))
        | ~ m1_pre_topc(X339,X338)
        | v2_struct_0(X338)
        | ~ l1_pre_topc(X338) )
      & ( ~ v4_tex_2(X339,X338)
        | v3_tex_2(X340,X338)
        | X340 != u1_struct_0(X339)
        | ~ m1_subset_1(X340,k1_zfmisc_1(u1_struct_0(X338)))
        | ~ m1_pre_topc(X339,X338)
        | v2_struct_0(X338)
        | ~ l1_pre_topc(X338) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_tex_2])])])])])).

cnf(c_0_7,plain,
    ( m1_pre_topc(esk85_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( X1 = u1_struct_0(esk85_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( v1_pre_topc(esk85_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk85_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,plain,
    ( v4_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ v3_tex_2(X1,X2)
    | X1 != u1_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ v4_tex_2(X1,esk1_0)
    | esk2_0 != u1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk85_2(esk1_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),c_0_10]),c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( u1_struct_0(esk85_2(esk1_0,esk2_0)) = esk2_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_8]),c_0_9])]),c_0_10]),c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v1_pre_topc(esk85_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_8]),c_0_9])]),c_0_10]),c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk85_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_8]),c_0_9])]),c_0_10]),c_0_11])).

cnf(c_0_21,plain,
    ( v4_tex_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v3_tex_2(u1_struct_0(X1),X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v3_tex_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( ~ v4_tex_2(esk85_2(esk1_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_22]),c_0_18]),c_0_8]),c_0_9])]),c_0_23]),c_0_11]),
    [proof]).
%------------------------------------------------------------------------------
