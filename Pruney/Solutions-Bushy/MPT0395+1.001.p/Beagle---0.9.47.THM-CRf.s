%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0395+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:14 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   46 (  69 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 138 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] : r1_setfam_1(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_setfam_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_22,plain,(
    ~ r1_setfam_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [C_34,B_35,A_36] :
      ( ~ v1_xboole_0(C_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [B_37,A_38,A_39] :
      ( ~ v1_xboole_0(B_37)
      | ~ r2_hidden(A_38,A_39)
      | ~ r1_tarski(A_39,B_37) ) ),
    inference(resolution,[status(thm)],[c_16,c_34])).

tff(c_49,plain,(
    ! [B_43,A_44,B_45] :
      ( ~ v1_xboole_0(B_43)
      | ~ r1_tarski(A_44,B_43)
      | r1_setfam_1(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_8,c_38])).

tff(c_52,plain,(
    ! [B_45] :
      ( ~ v1_xboole_0('#skF_4')
      | r1_setfam_1('#skF_3',B_45) ) ),
    inference(resolution,[status(thm)],[c_24,c_49])).

tff(c_53,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_10,plain,(
    ! [A_13] : r1_setfam_1(A_13,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_45,plain,(
    ! [A_40,C_41,B_42] :
      ( m1_subset_1(A_40,C_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(C_41))
      | ~ r2_hidden(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    ! [A_46,B_47,A_48] :
      ( m1_subset_1(A_46,B_47)
      | ~ r2_hidden(A_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(resolution,[status(thm)],[c_16,c_45])).

tff(c_60,plain,(
    ! [A_1,B_2,B_47] :
      ( m1_subset_1('#skF_1'(A_1,B_2),B_47)
      | ~ r1_tarski(A_1,B_47)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_8,c_54])).

tff(c_12,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1,B_2,C_11] :
      ( r2_hidden('#skF_2'(A_1,B_2,C_11),B_2)
      | ~ r2_hidden(C_11,A_1)
      | ~ r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_85,plain,(
    ! [C_61,A_62,B_63] :
      ( r1_tarski(C_61,'#skF_2'(A_62,B_63,C_61))
      | ~ r2_hidden(C_61,A_62)
      | ~ r1_setfam_1(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [A_1,B_2,D_10] :
      ( ~ r1_tarski('#skF_1'(A_1,B_2),D_10)
      | ~ r2_hidden(D_10,B_2)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_141,plain,(
    ! [A_77,B_78,A_79,B_80] :
      ( ~ r2_hidden('#skF_2'(A_77,B_78,'#skF_1'(A_79,B_80)),B_80)
      | r1_setfam_1(A_79,B_80)
      | ~ r2_hidden('#skF_1'(A_79,B_80),A_77)
      | ~ r1_setfam_1(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_85,c_6])).

tff(c_152,plain,(
    ! [A_81,B_82,A_83] :
      ( r1_setfam_1(A_81,B_82)
      | ~ r2_hidden('#skF_1'(A_81,B_82),A_83)
      | ~ r1_setfam_1(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_4,c_141])).

tff(c_173,plain,(
    ! [A_90,B_91,B_92] :
      ( r1_setfam_1(A_90,B_91)
      | ~ r1_setfam_1(B_92,B_91)
      | v1_xboole_0(B_92)
      | ~ m1_subset_1('#skF_1'(A_90,B_91),B_92) ) ),
    inference(resolution,[status(thm)],[c_12,c_152])).

tff(c_183,plain,(
    ! [B_93,B_94,A_95] :
      ( ~ r1_setfam_1(B_93,B_94)
      | v1_xboole_0(B_93)
      | ~ r1_tarski(A_95,B_93)
      | r1_setfam_1(A_95,B_94) ) ),
    inference(resolution,[status(thm)],[c_60,c_173])).

tff(c_187,plain,(
    ! [A_96,A_97] :
      ( v1_xboole_0(A_96)
      | ~ r1_tarski(A_97,A_96)
      | r1_setfam_1(A_97,A_96) ) ),
    inference(resolution,[status(thm)],[c_10,c_183])).

tff(c_196,plain,
    ( v1_xboole_0('#skF_4')
    | r1_setfam_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_187])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_53,c_196])).

tff(c_203,plain,(
    ! [B_45] : r1_setfam_1('#skF_3',B_45) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_22])).

%------------------------------------------------------------------------------
