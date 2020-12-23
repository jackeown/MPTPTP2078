%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:01 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 492 expanded)
%              Number of leaves         :   36 ( 174 expanded)
%              Depth                    :   14
%              Number of atoms          :  181 ( 940 expanded)
%              Number of equality atoms :   61 ( 238 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(c_1401,plain,(
    ! [A_185,B_186] :
      ( r2_hidden('#skF_1'(A_185,B_186),A_185)
      | r1_tarski(A_185,B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1414,plain,(
    ! [A_185] : r1_tarski(A_185,A_185) ),
    inference(resolution,[status(thm)],[c_1401,c_4])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_97,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_117,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_97])).

tff(c_168,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_183,plain,(
    ! [C_63] :
      ( ~ r1_xboole_0('#skF_5','#skF_6')
      | ~ r2_hidden(C_63,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_168])).

tff(c_189,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_1109,plain,(
    ! [A_157,B_158] :
      ( r2_hidden('#skF_2'(A_157,B_158),k3_xboole_0(A_157,B_158))
      | r1_xboole_0(A_157,B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1131,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_1109])).

tff(c_1137,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_1131])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1274,plain,(
    ! [B_174] :
      ( r2_hidden('#skF_2'('#skF_5','#skF_6'),B_174)
      | ~ r1_tarski('#skF_5',B_174) ) ),
    inference(resolution,[status(thm)],[c_1137,c_2])).

tff(c_443,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_2'(A_105,B_106),k3_xboole_0(A_105,B_106))
      | r1_xboole_0(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_471,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_443])).

tff(c_478,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_471])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_116,plain,(
    ! [A_17,B_18] : k3_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = A_17 ),
    inference(resolution,[status(thm)],[c_18,c_97])).

tff(c_388,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r1_xboole_0(A_95,k2_xboole_0(A_95,B_96))
      | ~ r2_hidden(C_97,A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_168])).

tff(c_391,plain,(
    ! [C_97,A_19,B_96] :
      ( ~ r2_hidden(C_97,A_19)
      | k4_xboole_0(A_19,k2_xboole_0(A_19,B_96)) != A_19 ) ),
    inference(resolution,[status(thm)],[c_22,c_388])).

tff(c_393,plain,(
    ! [C_97,A_19] :
      ( ~ r2_hidden(C_97,A_19)
      | k1_xboole_0 != A_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_391])).

tff(c_486,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_478,c_393])).

tff(c_42,plain,(
    ! [B_36,A_35] :
      ( r1_tarski(k1_setfam_1(B_36),k1_setfam_1(A_35))
      | k1_xboole_0 = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_72,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_83,plain,(
    r1_tarski('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_72])).

tff(c_113,plain,(
    k3_xboole_0('#skF_6',k1_zfmisc_1('#skF_4')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_83,c_97])).

tff(c_177,plain,(
    ! [C_63] :
      ( ~ r1_xboole_0('#skF_6',k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(C_63,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_168])).

tff(c_196,plain,(
    ~ r1_xboole_0('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_468,plain,
    ( r2_hidden('#skF_2'('#skF_6',k1_zfmisc_1('#skF_4')),'#skF_6')
    | r1_xboole_0('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_443])).

tff(c_477,plain,(
    r2_hidden('#skF_2'('#skF_6',k1_zfmisc_1('#skF_4')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_468])).

tff(c_496,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_477,c_393])).

tff(c_409,plain,(
    ! [A_102,B_103] :
      ( k6_setfam_1(A_102,B_103) = k1_setfam_1(B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k1_zfmisc_1(A_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_426,plain,(
    k6_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_409])).

tff(c_852,plain,(
    ! [A_130,B_131] :
      ( k8_setfam_1(A_130,B_131) = k6_setfam_1(A_130,B_131)
      | k1_xboole_0 = B_131
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k1_zfmisc_1(A_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_874,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k6_setfam_1('#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_852])).

tff(c_887,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_874])).

tff(c_888,plain,(
    k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_496,c_887])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_425,plain,(
    k6_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_409])).

tff(c_871,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = k6_setfam_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_852])).

tff(c_884,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_871])).

tff(c_885,plain,(
    k8_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_486,c_884])).

tff(c_44,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k8_setfam_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_892,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_44])).

tff(c_912,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_892])).

tff(c_915,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_912])).

tff(c_921,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_915])).

tff(c_923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_486,c_921])).

tff(c_924,plain,(
    ! [C_63] : ~ r2_hidden(C_63,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_1285,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1274,c_924])).

tff(c_1296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1285])).

tff(c_1299,plain,(
    ! [C_175] : ~ r2_hidden(C_175,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_1304,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12,c_1299])).

tff(c_1308,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | A_11 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1304,c_12])).

tff(c_1307,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1304,c_16])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1594,plain,(
    ! [A_209,B_210,B_211] :
      ( ~ r1_xboole_0(A_209,B_210)
      | r1_tarski(k3_xboole_0(A_209,B_210),B_211) ) ),
    inference(resolution,[status(thm)],[c_1401,c_10])).

tff(c_1645,plain,(
    ! [A_216,B_217,B_218] :
      ( ~ r1_xboole_0(A_216,k2_xboole_0(A_216,B_217))
      | r1_tarski(A_216,B_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_1594])).

tff(c_1651,plain,(
    ! [A_19,B_218,B_217] :
      ( r1_tarski(A_19,B_218)
      | k4_xboole_0(A_19,k2_xboole_0(A_19,B_217)) != A_19 ) ),
    inference(resolution,[status(thm)],[c_22,c_1645])).

tff(c_1658,plain,(
    ! [A_219,B_220] :
      ( r1_tarski(A_219,B_220)
      | A_219 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1307,c_1651])).

tff(c_1450,plain,(
    ~ r1_xboole_0('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_1482,plain,(
    ! [A_201,B_202] :
      ( r2_hidden('#skF_2'(A_201,B_202),k3_xboole_0(A_201,B_202))
      | r1_xboole_0(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1501,plain,
    ( r2_hidden('#skF_2'('#skF_6',k1_zfmisc_1('#skF_4')),'#skF_6')
    | r1_xboole_0('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_1482])).

tff(c_1506,plain,(
    r2_hidden('#skF_2'('#skF_6',k1_zfmisc_1('#skF_4')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1450,c_1501])).

tff(c_1613,plain,(
    ! [B_212] :
      ( r2_hidden('#skF_2'('#skF_6',k1_zfmisc_1('#skF_4')),B_212)
      | ~ r1_tarski('#skF_6',B_212) ) ),
    inference(resolution,[status(thm)],[c_1506,c_2])).

tff(c_1297,plain,(
    ! [C_63] : ~ r2_hidden(C_63,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_1628,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1613,c_1297])).

tff(c_1668,plain,(
    '#skF_5' != '#skF_6' ),
    inference(resolution,[status(thm)],[c_1658,c_1628])).

tff(c_1568,plain,(
    ! [A_206,B_207] :
      ( k6_setfam_1(A_206,B_207) = k1_setfam_1(B_207)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k1_zfmisc_1(A_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1582,plain,(
    k6_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_1568])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( k8_setfam_1(A_24,B_25) = k6_setfam_1(A_24,B_25)
      | k1_xboole_0 = B_25
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2113,plain,(
    ! [A_255,B_256] :
      ( k8_setfam_1(A_255,B_256) = k6_setfam_1(A_255,B_256)
      | B_256 = '#skF_5'
      | ~ m1_subset_1(B_256,k1_zfmisc_1(k1_zfmisc_1(A_255))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1304,c_30])).

tff(c_2136,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k6_setfam_1('#skF_4','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_2113])).

tff(c_2146,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1582,c_2136])).

tff(c_2147,plain,(
    k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1668,c_2146])).

tff(c_26,plain,(
    ! [A_23] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_24] :
      ( k8_setfam_1(A_24,k1_xboole_0) = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    ! [A_24] : k8_setfam_1(A_24,k1_xboole_0) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_1309,plain,(
    ! [A_24] : k8_setfam_1(A_24,'#skF_5') = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1304,c_52])).

tff(c_1363,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1309,c_44])).

tff(c_2149,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_1363])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k8_setfam_1(A_26,B_27),k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2153,plain,
    ( m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2147,c_32])).

tff(c_2157,plain,(
    m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2153])).

tff(c_36,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2204,plain,(
    r1_tarski(k1_setfam_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2157,c_36])).

tff(c_2209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2149,c_2204])).

tff(c_2212,plain,(
    ! [C_257] : ~ r2_hidden(C_257,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_2222,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1308,c_2212])).

tff(c_2233,plain,(
    ! [A_24] : k8_setfam_1(A_24,'#skF_6') = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2222,c_1309])).

tff(c_2323,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2233,c_1363])).

tff(c_2326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_2323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.72  
% 4.11/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.72  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 4.11/1.72  
% 4.11/1.72  %Foreground sorts:
% 4.11/1.72  
% 4.11/1.72  
% 4.11/1.72  %Background operators:
% 4.11/1.72  
% 4.11/1.72  
% 4.11/1.72  %Foreground operators:
% 4.11/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.11/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.11/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.11/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.11/1.72  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 4.11/1.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.11/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.11/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.11/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.11/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.11/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.11/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.11/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.11/1.72  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 4.11/1.72  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.11/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.11/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.11/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.11/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.11/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.11/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.11/1.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.11/1.72  
% 4.11/1.74  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.11/1.74  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.11/1.74  tff(f_115, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 4.11/1.74  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.11/1.74  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.11/1.74  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.11/1.74  tff(f_66, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.11/1.74  tff(f_62, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.11/1.74  tff(f_105, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 4.11/1.74  tff(f_93, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.11/1.74  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 4.11/1.74  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 4.11/1.74  tff(f_70, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.11/1.74  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 4.11/1.74  tff(c_1401, plain, (![A_185, B_186]: (r2_hidden('#skF_1'(A_185, B_186), A_185) | r1_tarski(A_185, B_186))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.74  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.74  tff(c_1414, plain, (![A_185]: (r1_tarski(A_185, A_185))), inference(resolution, [status(thm)], [c_1401, c_4])).
% 4.11/1.74  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.11/1.74  tff(c_46, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.11/1.74  tff(c_97, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.11/1.74  tff(c_117, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_97])).
% 4.11/1.74  tff(c_168, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.11/1.74  tff(c_183, plain, (![C_63]: (~r1_xboole_0('#skF_5', '#skF_6') | ~r2_hidden(C_63, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_168])).
% 4.11/1.74  tff(c_189, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_183])).
% 4.11/1.74  tff(c_1109, plain, (![A_157, B_158]: (r2_hidden('#skF_2'(A_157, B_158), k3_xboole_0(A_157, B_158)) | r1_xboole_0(A_157, B_158))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.11/1.74  tff(c_1131, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | r1_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_117, c_1109])).
% 4.11/1.74  tff(c_1137, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_189, c_1131])).
% 4.11/1.74  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.74  tff(c_1274, plain, (![B_174]: (r2_hidden('#skF_2'('#skF_5', '#skF_6'), B_174) | ~r1_tarski('#skF_5', B_174))), inference(resolution, [status(thm)], [c_1137, c_2])).
% 4.11/1.74  tff(c_443, plain, (![A_105, B_106]: (r2_hidden('#skF_2'(A_105, B_106), k3_xboole_0(A_105, B_106)) | r1_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.11/1.74  tff(c_471, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | r1_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_117, c_443])).
% 4.11/1.74  tff(c_478, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_189, c_471])).
% 4.11/1.74  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.11/1.74  tff(c_22, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k4_xboole_0(A_19, B_20)!=A_19)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.11/1.74  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.11/1.74  tff(c_116, plain, (![A_17, B_18]: (k3_xboole_0(A_17, k2_xboole_0(A_17, B_18))=A_17)), inference(resolution, [status(thm)], [c_18, c_97])).
% 4.11/1.74  tff(c_388, plain, (![A_95, B_96, C_97]: (~r1_xboole_0(A_95, k2_xboole_0(A_95, B_96)) | ~r2_hidden(C_97, A_95))), inference(superposition, [status(thm), theory('equality')], [c_116, c_168])).
% 4.11/1.74  tff(c_391, plain, (![C_97, A_19, B_96]: (~r2_hidden(C_97, A_19) | k4_xboole_0(A_19, k2_xboole_0(A_19, B_96))!=A_19)), inference(resolution, [status(thm)], [c_22, c_388])).
% 4.11/1.74  tff(c_393, plain, (![C_97, A_19]: (~r2_hidden(C_97, A_19) | k1_xboole_0!=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_391])).
% 4.11/1.74  tff(c_486, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_478, c_393])).
% 4.11/1.74  tff(c_42, plain, (![B_36, A_35]: (r1_tarski(k1_setfam_1(B_36), k1_setfam_1(A_35)) | k1_xboole_0=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.11/1.74  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.11/1.74  tff(c_72, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.11/1.74  tff(c_83, plain, (r1_tarski('#skF_6', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_72])).
% 4.11/1.74  tff(c_113, plain, (k3_xboole_0('#skF_6', k1_zfmisc_1('#skF_4'))='#skF_6'), inference(resolution, [status(thm)], [c_83, c_97])).
% 4.11/1.74  tff(c_177, plain, (![C_63]: (~r1_xboole_0('#skF_6', k1_zfmisc_1('#skF_4')) | ~r2_hidden(C_63, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_168])).
% 4.11/1.74  tff(c_196, plain, (~r1_xboole_0('#skF_6', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_177])).
% 4.11/1.74  tff(c_468, plain, (r2_hidden('#skF_2'('#skF_6', k1_zfmisc_1('#skF_4')), '#skF_6') | r1_xboole_0('#skF_6', k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_443])).
% 4.11/1.74  tff(c_477, plain, (r2_hidden('#skF_2'('#skF_6', k1_zfmisc_1('#skF_4')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_196, c_468])).
% 4.11/1.74  tff(c_496, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_477, c_393])).
% 4.11/1.74  tff(c_409, plain, (![A_102, B_103]: (k6_setfam_1(A_102, B_103)=k1_setfam_1(B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(k1_zfmisc_1(A_102))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.11/1.74  tff(c_426, plain, (k6_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_409])).
% 4.11/1.74  tff(c_852, plain, (![A_130, B_131]: (k8_setfam_1(A_130, B_131)=k6_setfam_1(A_130, B_131) | k1_xboole_0=B_131 | ~m1_subset_1(B_131, k1_zfmisc_1(k1_zfmisc_1(A_130))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.11/1.74  tff(c_874, plain, (k8_setfam_1('#skF_4', '#skF_6')=k6_setfam_1('#skF_4', '#skF_6') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_48, c_852])).
% 4.11/1.74  tff(c_887, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_426, c_874])).
% 4.11/1.74  tff(c_888, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_496, c_887])).
% 4.11/1.74  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.11/1.74  tff(c_425, plain, (k6_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_409])).
% 4.11/1.74  tff(c_871, plain, (k8_setfam_1('#skF_4', '#skF_5')=k6_setfam_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_852])).
% 4.11/1.74  tff(c_884, plain, (k8_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_425, c_871])).
% 4.11/1.74  tff(c_885, plain, (k8_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_486, c_884])).
% 4.11/1.74  tff(c_44, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k8_setfam_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.11/1.74  tff(c_892, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k1_setfam_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_885, c_44])).
% 4.11/1.74  tff(c_912, plain, (~r1_tarski(k1_setfam_1('#skF_6'), k1_setfam_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_888, c_892])).
% 4.11/1.74  tff(c_915, plain, (k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_912])).
% 4.11/1.74  tff(c_921, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_915])).
% 4.11/1.74  tff(c_923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_486, c_921])).
% 4.11/1.74  tff(c_924, plain, (![C_63]: (~r2_hidden(C_63, '#skF_6'))), inference(splitRight, [status(thm)], [c_177])).
% 4.11/1.74  tff(c_1285, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1274, c_924])).
% 4.11/1.74  tff(c_1296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1285])).
% 4.11/1.74  tff(c_1299, plain, (![C_175]: (~r2_hidden(C_175, '#skF_5'))), inference(splitRight, [status(thm)], [c_183])).
% 4.11/1.74  tff(c_1304, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_12, c_1299])).
% 4.11/1.74  tff(c_1308, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | A_11='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1304, c_12])).
% 4.11/1.74  tff(c_1307, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1304, c_16])).
% 4.11/1.74  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.11/1.74  tff(c_1594, plain, (![A_209, B_210, B_211]: (~r1_xboole_0(A_209, B_210) | r1_tarski(k3_xboole_0(A_209, B_210), B_211))), inference(resolution, [status(thm)], [c_1401, c_10])).
% 4.11/1.74  tff(c_1645, plain, (![A_216, B_217, B_218]: (~r1_xboole_0(A_216, k2_xboole_0(A_216, B_217)) | r1_tarski(A_216, B_218))), inference(superposition, [status(thm), theory('equality')], [c_116, c_1594])).
% 4.11/1.74  tff(c_1651, plain, (![A_19, B_218, B_217]: (r1_tarski(A_19, B_218) | k4_xboole_0(A_19, k2_xboole_0(A_19, B_217))!=A_19)), inference(resolution, [status(thm)], [c_22, c_1645])).
% 4.11/1.74  tff(c_1658, plain, (![A_219, B_220]: (r1_tarski(A_219, B_220) | A_219!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1307, c_1651])).
% 4.11/1.74  tff(c_1450, plain, (~r1_xboole_0('#skF_6', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_177])).
% 4.11/1.74  tff(c_1482, plain, (![A_201, B_202]: (r2_hidden('#skF_2'(A_201, B_202), k3_xboole_0(A_201, B_202)) | r1_xboole_0(A_201, B_202))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.11/1.74  tff(c_1501, plain, (r2_hidden('#skF_2'('#skF_6', k1_zfmisc_1('#skF_4')), '#skF_6') | r1_xboole_0('#skF_6', k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_1482])).
% 4.11/1.74  tff(c_1506, plain, (r2_hidden('#skF_2'('#skF_6', k1_zfmisc_1('#skF_4')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1450, c_1501])).
% 4.11/1.74  tff(c_1613, plain, (![B_212]: (r2_hidden('#skF_2'('#skF_6', k1_zfmisc_1('#skF_4')), B_212) | ~r1_tarski('#skF_6', B_212))), inference(resolution, [status(thm)], [c_1506, c_2])).
% 4.11/1.74  tff(c_1297, plain, (![C_63]: (~r2_hidden(C_63, '#skF_5'))), inference(splitRight, [status(thm)], [c_183])).
% 4.11/1.74  tff(c_1628, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_1613, c_1297])).
% 4.11/1.74  tff(c_1668, plain, ('#skF_5'!='#skF_6'), inference(resolution, [status(thm)], [c_1658, c_1628])).
% 4.11/1.74  tff(c_1568, plain, (![A_206, B_207]: (k6_setfam_1(A_206, B_207)=k1_setfam_1(B_207) | ~m1_subset_1(B_207, k1_zfmisc_1(k1_zfmisc_1(A_206))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.11/1.74  tff(c_1582, plain, (k6_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_1568])).
% 4.11/1.74  tff(c_30, plain, (![A_24, B_25]: (k8_setfam_1(A_24, B_25)=k6_setfam_1(A_24, B_25) | k1_xboole_0=B_25 | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.11/1.74  tff(c_2113, plain, (![A_255, B_256]: (k8_setfam_1(A_255, B_256)=k6_setfam_1(A_255, B_256) | B_256='#skF_5' | ~m1_subset_1(B_256, k1_zfmisc_1(k1_zfmisc_1(A_255))))), inference(demodulation, [status(thm), theory('equality')], [c_1304, c_30])).
% 4.11/1.74  tff(c_2136, plain, (k8_setfam_1('#skF_4', '#skF_6')=k6_setfam_1('#skF_4', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_48, c_2113])).
% 4.11/1.74  tff(c_2146, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1582, c_2136])).
% 4.11/1.74  tff(c_2147, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1668, c_2146])).
% 4.11/1.74  tff(c_26, plain, (![A_23]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.11/1.74  tff(c_28, plain, (![A_24]: (k8_setfam_1(A_24, k1_xboole_0)=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.11/1.74  tff(c_52, plain, (![A_24]: (k8_setfam_1(A_24, k1_xboole_0)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 4.11/1.74  tff(c_1309, plain, (![A_24]: (k8_setfam_1(A_24, '#skF_5')=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_1304, c_52])).
% 4.11/1.74  tff(c_1363, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1309, c_44])).
% 4.11/1.74  tff(c_2149, plain, (~r1_tarski(k1_setfam_1('#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2147, c_1363])).
% 4.11/1.74  tff(c_32, plain, (![A_26, B_27]: (m1_subset_1(k8_setfam_1(A_26, B_27), k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.11/1.74  tff(c_2153, plain, (m1_subset_1(k1_setfam_1('#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2147, c_32])).
% 4.11/1.74  tff(c_2157, plain, (m1_subset_1(k1_setfam_1('#skF_6'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2153])).
% 4.11/1.74  tff(c_36, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.11/1.74  tff(c_2204, plain, (r1_tarski(k1_setfam_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_2157, c_36])).
% 4.11/1.74  tff(c_2209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2149, c_2204])).
% 4.11/1.74  tff(c_2212, plain, (![C_257]: (~r2_hidden(C_257, '#skF_6'))), inference(splitRight, [status(thm)], [c_177])).
% 4.11/1.74  tff(c_2222, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1308, c_2212])).
% 4.11/1.74  tff(c_2233, plain, (![A_24]: (k8_setfam_1(A_24, '#skF_6')=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_2222, c_1309])).
% 4.11/1.74  tff(c_2323, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2233, c_1363])).
% 4.11/1.74  tff(c_2326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1414, c_2323])).
% 4.11/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.74  
% 4.11/1.74  Inference rules
% 4.11/1.74  ----------------------
% 4.11/1.74  #Ref     : 0
% 4.11/1.74  #Sup     : 526
% 4.11/1.74  #Fact    : 0
% 4.11/1.74  #Define  : 0
% 4.11/1.74  #Split   : 7
% 4.11/1.74  #Chain   : 0
% 4.11/1.74  #Close   : 0
% 4.11/1.74  
% 4.11/1.74  Ordering : KBO
% 4.11/1.74  
% 4.11/1.74  Simplification rules
% 4.11/1.74  ----------------------
% 4.11/1.74  #Subsume      : 74
% 4.11/1.74  #Demod        : 138
% 4.11/1.74  #Tautology    : 200
% 4.11/1.74  #SimpNegUnit  : 16
% 4.11/1.74  #BackRed      : 31
% 4.11/1.74  
% 4.11/1.74  #Partial instantiations: 0
% 4.11/1.74  #Strategies tried      : 1
% 4.11/1.74  
% 4.11/1.74  Timing (in seconds)
% 4.11/1.74  ----------------------
% 4.11/1.75  Preprocessing        : 0.34
% 4.11/1.75  Parsing              : 0.18
% 4.11/1.75  CNF conversion       : 0.02
% 4.11/1.75  Main loop            : 0.62
% 4.11/1.75  Inferencing          : 0.24
% 4.11/1.75  Reduction            : 0.19
% 4.11/1.75  Demodulation         : 0.13
% 4.11/1.75  BG Simplification    : 0.03
% 4.11/1.75  Subsumption          : 0.09
% 4.11/1.75  Abstraction          : 0.03
% 4.11/1.75  MUC search           : 0.00
% 4.11/1.75  Cooper               : 0.00
% 4.11/1.75  Total                : 1.01
% 4.11/1.75  Index Insertion      : 0.00
% 4.11/1.75  Index Deletion       : 0.00
% 4.11/1.75  Index Matching       : 0.00
% 4.11/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
