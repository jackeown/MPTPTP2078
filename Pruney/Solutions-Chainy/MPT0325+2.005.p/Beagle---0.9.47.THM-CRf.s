%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:21 EST 2020

% Result     : Theorem 11.47s
% Output     : CNFRefutation 11.47s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 654 expanded)
%              Number of leaves         :   36 ( 229 expanded)
%              Depth                    :   18
%              Number of atoms          :  134 ( 938 expanded)
%              Number of equality atoms :  107 ( 687 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_71,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_40,plain,(
    ! [A_47] : k2_zfmisc_1(A_47,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12596,plain,(
    ! [A_3470,B_3471] :
      ( k4_xboole_0(A_3470,B_3471) = k1_xboole_0
      | ~ r1_tarski(A_3470,B_3471) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12612,plain,(
    ! [A_7,B_8] : k4_xboole_0(k3_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_12596])).

tff(c_52,plain,(
    ! [C_58,A_56,B_57] : k4_xboole_0(k2_zfmisc_1(C_58,A_56),k2_zfmisc_1(C_58,B_57)) = k2_zfmisc_1(C_58,k4_xboole_0(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_213,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,B_75)
      | k4_xboole_0(A_74,B_75) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,
    ( ~ r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_133,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_221,plain,(
    k4_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_213,c_133])).

tff(c_20,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1308,plain,(
    ! [A_143,C_144,B_145,D_146] : k3_xboole_0(k2_zfmisc_1(A_143,C_144),k2_zfmisc_1(B_145,D_146)) = k2_zfmisc_1(k3_xboole_0(A_143,B_145),k3_xboole_0(C_144,D_146)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_299,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_312,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_299])).

tff(c_1314,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_312])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1441,plain,(
    ! [A_147,B_148,C_149,D_150] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_147,B_148),k3_xboole_0(C_149,D_150)),k2_zfmisc_1(A_147,C_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_10])).

tff(c_1592,plain,(
    ! [A_154,B_155,A_156] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_154,B_155),A_156),k2_zfmisc_1(A_154,A_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1441])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1783,plain,(
    ! [A_166,B_167,A_168] : k4_xboole_0(k2_zfmisc_1(k3_xboole_0(A_166,B_167),A_168),k2_zfmisc_1(A_166,A_168)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1592,c_6])).

tff(c_1796,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2','#skF_4'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1314,c_1783])).

tff(c_2017,plain,(
    k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_4'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1796,c_52])).

tff(c_38,plain,(
    ! [B_48,A_47] :
      ( k1_xboole_0 = B_48
      | k1_xboole_0 = A_47
      | k2_zfmisc_1(A_47,B_48) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2091,plain,
    ( k4_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_4')) = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2017,c_38])).

tff(c_2094,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2091])).

tff(c_42,plain,(
    ! [B_48] : k2_zfmisc_1(k1_xboole_0,B_48) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2123,plain,(
    ! [B_48] : k2_zfmisc_1('#skF_1',B_48) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2094,c_2094,c_42])).

tff(c_56,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2124,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2094,c_56])).

tff(c_2262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2123,c_2124])).

tff(c_2264,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2091])).

tff(c_12,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3094,plain,(
    ! [A_199,C_200,B_201,D_202] : k2_xboole_0(k2_zfmisc_1(A_199,C_200),k2_zfmisc_1(k3_xboole_0(A_199,B_201),k3_xboole_0(C_200,D_202))) = k2_zfmisc_1(A_199,C_200) ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_12])).

tff(c_3385,plain,(
    ! [A_208,A_209,B_210] : k2_xboole_0(k2_zfmisc_1(A_208,A_209),k2_zfmisc_1(k3_xboole_0(A_208,B_210),A_209)) = k2_zfmisc_1(A_208,A_209) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3094])).

tff(c_3421,plain,(
    k2_xboole_0(k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2','#skF_4')),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1314,c_3385])).

tff(c_22,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_284,plain,(
    ! [A_84,B_85] : k3_tarski(k2_tarski(A_84,B_85)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_317,plain,(
    ! [B_88,A_89] : k3_tarski(k2_tarski(B_88,A_89)) = k2_xboole_0(A_89,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_284])).

tff(c_36,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_323,plain,(
    ! [B_88,A_89] : k2_xboole_0(B_88,A_89) = k2_xboole_0(A_89,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_36])).

tff(c_678,plain,(
    ! [C_115,A_116,B_117] : k2_xboole_0(k2_zfmisc_1(C_115,A_116),k2_zfmisc_1(C_115,B_117)) = k2_zfmisc_1(C_115,k2_xboole_0(A_116,B_117)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_720,plain,(
    ! [C_115,B_117,A_116] : k2_xboole_0(k2_zfmisc_1(C_115,B_117),k2_zfmisc_1(C_115,A_116)) = k2_zfmisc_1(C_115,k2_xboole_0(A_116,B_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_678])).

tff(c_11332,plain,(
    k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_4'))) = k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3421,c_720])).

tff(c_11364,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_11332])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3533,plain,(
    ! [A_213,C_214,B_215,D_216] : k5_xboole_0(k2_zfmisc_1(A_213,C_214),k2_zfmisc_1(k3_xboole_0(A_213,B_215),k3_xboole_0(C_214,D_216))) = k4_xboole_0(k2_zfmisc_1(A_213,C_214),k2_zfmisc_1(B_215,D_216)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_8])).

tff(c_3618,plain,(
    ! [A_1,C_214,D_216] : k5_xboole_0(k2_zfmisc_1(A_1,C_214),k2_zfmisc_1(A_1,k3_xboole_0(C_214,D_216))) = k4_xboole_0(k2_zfmisc_1(A_1,C_214),k2_zfmisc_1(A_1,D_216)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3533])).

tff(c_3645,plain,(
    ! [A_1,C_214,D_216] : k5_xboole_0(k2_zfmisc_1(A_1,C_214),k2_zfmisc_1(A_1,k3_xboole_0(C_214,D_216))) = k2_zfmisc_1(A_1,k4_xboole_0(C_214,D_216)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3618])).

tff(c_11392,plain,(
    k5_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11364,c_3645])).

tff(c_11479,plain,(
    k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_11392])).

tff(c_11580,plain,
    ( k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11479,c_38])).

tff(c_11603,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2264,c_11580])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_313,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_299])).

tff(c_11613,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_11603,c_313])).

tff(c_11620,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11613,c_1314])).

tff(c_50,plain,(
    ! [A_56,C_58,B_57] : k4_xboole_0(k2_zfmisc_1(A_56,C_58),k2_zfmisc_1(B_57,C_58)) = k2_zfmisc_1(k4_xboole_0(A_56,B_57),C_58) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3621,plain,(
    ! [A_213,A_1,B_215] : k5_xboole_0(k2_zfmisc_1(A_213,A_1),k2_zfmisc_1(k3_xboole_0(A_213,B_215),A_1)) = k4_xboole_0(k2_zfmisc_1(A_213,A_1),k2_zfmisc_1(B_215,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3533])).

tff(c_3646,plain,(
    ! [A_213,A_1,B_215] : k5_xboole_0(k2_zfmisc_1(A_213,A_1),k2_zfmisc_1(k3_xboole_0(A_213,B_215),A_1)) = k2_zfmisc_1(k4_xboole_0(A_213,B_215),A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3621])).

tff(c_11729,plain,(
    k5_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11620,c_3646])).

tff(c_11819,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_11729])).

tff(c_11919,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11819,c_38])).

tff(c_11942,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_11919])).

tff(c_11969,plain,(
    ! [A_47] : k2_zfmisc_1(A_47,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11942,c_11942,c_40])).

tff(c_11971,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11942,c_56])).

tff(c_12484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11969,c_11971])).

tff(c_12486,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_12566,plain,(
    ! [A_3468,B_3469] :
      ( k3_xboole_0(A_3468,B_3469) = A_3468
      | ~ r1_tarski(A_3468,B_3469) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12576,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12486,c_12566])).

tff(c_13623,plain,(
    ! [A_3533,C_3534,B_3535,D_3536] : k3_xboole_0(k2_zfmisc_1(A_3533,C_3534),k2_zfmisc_1(B_3535,D_3536)) = k2_zfmisc_1(k3_xboole_0(A_3533,B_3535),k3_xboole_0(C_3534,D_3536)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12583,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_14])).

tff(c_13629,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13623,c_12583])).

tff(c_13702,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12576,c_13629])).

tff(c_13745,plain,(
    ! [A_56] : k4_xboole_0(k2_zfmisc_1('#skF_1',A_56),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1('#skF_1',k4_xboole_0(A_56,k3_xboole_0('#skF_2','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_13702,c_52])).

tff(c_16533,plain,(
    ! [A_3628] : k2_zfmisc_1('#skF_1',k4_xboole_0(A_3628,k3_xboole_0('#skF_2','#skF_4'))) = k2_zfmisc_1('#skF_1',k4_xboole_0(A_3628,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_13745])).

tff(c_16625,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',k4_xboole_0(k3_xboole_0(k3_xboole_0('#skF_2','#skF_4'),B_8),'#skF_2')) = k2_zfmisc_1('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12612,c_16533])).

tff(c_16648,plain,(
    ! [B_3629] : k2_zfmisc_1('#skF_1',k4_xboole_0(k3_xboole_0(k3_xboole_0('#skF_2','#skF_4'),B_3629),'#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16625])).

tff(c_16758,plain,(
    ! [B_3629] :
      ( k4_xboole_0(k3_xboole_0(k3_xboole_0('#skF_2','#skF_4'),B_3629),'#skF_2') = k1_xboole_0
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16648,c_38])).

tff(c_16763,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_16758])).

tff(c_16802,plain,(
    ! [B_48] : k2_zfmisc_1('#skF_1',B_48) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16763,c_16763,c_42])).

tff(c_16803,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16763,c_56])).

tff(c_16827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16802,c_16803])).

tff(c_16829,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16758])).

tff(c_12667,plain,(
    ! [A_3479,B_3480] :
      ( r1_tarski(A_3479,B_3480)
      | k4_xboole_0(A_3479,B_3480) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12485,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_12683,plain,(
    k4_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12667,c_12485])).

tff(c_16048,plain,(
    ! [A_3613,C_3614,B_3615,D_3616] : k5_xboole_0(k2_zfmisc_1(A_3613,C_3614),k2_zfmisc_1(k3_xboole_0(A_3613,B_3615),k3_xboole_0(C_3614,D_3616))) = k4_xboole_0(k2_zfmisc_1(A_3613,C_3614),k2_zfmisc_1(B_3615,D_3616)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13623,c_8])).

tff(c_16130,plain,(
    ! [A_1,C_3614,D_3616] : k5_xboole_0(k2_zfmisc_1(A_1,C_3614),k2_zfmisc_1(A_1,k3_xboole_0(C_3614,D_3616))) = k4_xboole_0(k2_zfmisc_1(A_1,C_3614),k2_zfmisc_1(A_1,D_3616)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16048])).

tff(c_22107,plain,(
    ! [A_6721,C_6722,D_6723] : k5_xboole_0(k2_zfmisc_1(A_6721,C_6722),k2_zfmisc_1(A_6721,k3_xboole_0(C_6722,D_6723))) = k2_zfmisc_1(A_6721,k4_xboole_0(C_6722,D_6723)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16130])).

tff(c_22197,plain,(
    k5_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13702,c_22107])).

tff(c_22265,plain,(
    k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22197])).

tff(c_22379,plain,
    ( k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_22265,c_38])).

tff(c_22414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16829,c_12683,c_22379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:05:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.47/4.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.47/4.47  
% 11.47/4.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.47/4.48  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.47/4.48  
% 11.47/4.48  %Foreground sorts:
% 11.47/4.48  
% 11.47/4.48  
% 11.47/4.48  %Background operators:
% 11.47/4.48  
% 11.47/4.48  
% 11.47/4.48  %Foreground operators:
% 11.47/4.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.47/4.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.47/4.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.47/4.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.47/4.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.47/4.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.47/4.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.47/4.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.47/4.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.47/4.48  tff('#skF_2', type, '#skF_2': $i).
% 11.47/4.48  tff('#skF_3', type, '#skF_3': $i).
% 11.47/4.48  tff('#skF_1', type, '#skF_1': $i).
% 11.47/4.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.47/4.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.47/4.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.47/4.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.47/4.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.47/4.48  tff('#skF_4', type, '#skF_4': $i).
% 11.47/4.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.47/4.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.47/4.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.47/4.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.47/4.48  
% 11.47/4.50  tff(f_71, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.47/4.50  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 11.47/4.50  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.47/4.50  tff(f_81, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 11.47/4.50  tff(f_90, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 11.47/4.50  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.47/4.50  tff(f_77, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 11.47/4.50  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.47/4.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.47/4.50  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 11.47/4.50  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.47/4.50  tff(f_65, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.47/4.50  tff(f_75, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 11.47/4.50  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.47/4.50  tff(c_40, plain, (![A_47]: (k2_zfmisc_1(A_47, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.47/4.50  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.47/4.50  tff(c_12596, plain, (![A_3470, B_3471]: (k4_xboole_0(A_3470, B_3471)=k1_xboole_0 | ~r1_tarski(A_3470, B_3471))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.47/4.50  tff(c_12612, plain, (![A_7, B_8]: (k4_xboole_0(k3_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_12596])).
% 11.47/4.50  tff(c_52, plain, (![C_58, A_56, B_57]: (k4_xboole_0(k2_zfmisc_1(C_58, A_56), k2_zfmisc_1(C_58, B_57))=k2_zfmisc_1(C_58, k4_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.47/4.50  tff(c_213, plain, (![A_74, B_75]: (r1_tarski(A_74, B_75) | k4_xboole_0(A_74, B_75)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.47/4.50  tff(c_54, plain, (~r1_tarski('#skF_2', '#skF_4') | ~r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.47/4.50  tff(c_133, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 11.47/4.50  tff(c_221, plain, (k4_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_213, c_133])).
% 11.47/4.50  tff(c_20, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.47/4.50  tff(c_1308, plain, (![A_143, C_144, B_145, D_146]: (k3_xboole_0(k2_zfmisc_1(A_143, C_144), k2_zfmisc_1(B_145, D_146))=k2_zfmisc_1(k3_xboole_0(A_143, B_145), k3_xboole_0(C_144, D_146)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.47/4.50  tff(c_58, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.47/4.50  tff(c_299, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=A_86 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.47/4.50  tff(c_312, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_299])).
% 11.47/4.50  tff(c_1314, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1308, c_312])).
% 11.47/4.50  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.47/4.50  tff(c_1441, plain, (![A_147, B_148, C_149, D_150]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_147, B_148), k3_xboole_0(C_149, D_150)), k2_zfmisc_1(A_147, C_149)))), inference(superposition, [status(thm), theory('equality')], [c_1308, c_10])).
% 11.47/4.50  tff(c_1592, plain, (![A_154, B_155, A_156]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_154, B_155), A_156), k2_zfmisc_1(A_154, A_156)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1441])).
% 11.47/4.50  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.47/4.50  tff(c_1783, plain, (![A_166, B_167, A_168]: (k4_xboole_0(k2_zfmisc_1(k3_xboole_0(A_166, B_167), A_168), k2_zfmisc_1(A_166, A_168))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1592, c_6])).
% 11.47/4.50  tff(c_1796, plain, (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', '#skF_4')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1314, c_1783])).
% 11.47/4.50  tff(c_2017, plain, (k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_4')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1796, c_52])).
% 11.47/4.50  tff(c_38, plain, (![B_48, A_47]: (k1_xboole_0=B_48 | k1_xboole_0=A_47 | k2_zfmisc_1(A_47, B_48)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.47/4.50  tff(c_2091, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_4'))=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2017, c_38])).
% 11.47/4.50  tff(c_2094, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_2091])).
% 11.47/4.50  tff(c_42, plain, (![B_48]: (k2_zfmisc_1(k1_xboole_0, B_48)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.47/4.50  tff(c_2123, plain, (![B_48]: (k2_zfmisc_1('#skF_1', B_48)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2094, c_2094, c_42])).
% 11.47/4.50  tff(c_56, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.47/4.50  tff(c_2124, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2094, c_56])).
% 11.47/4.50  tff(c_2262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2123, c_2124])).
% 11.47/4.50  tff(c_2264, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_2091])).
% 11.47/4.50  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k3_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.47/4.50  tff(c_3094, plain, (![A_199, C_200, B_201, D_202]: (k2_xboole_0(k2_zfmisc_1(A_199, C_200), k2_zfmisc_1(k3_xboole_0(A_199, B_201), k3_xboole_0(C_200, D_202)))=k2_zfmisc_1(A_199, C_200))), inference(superposition, [status(thm), theory('equality')], [c_1308, c_12])).
% 11.47/4.50  tff(c_3385, plain, (![A_208, A_209, B_210]: (k2_xboole_0(k2_zfmisc_1(A_208, A_209), k2_zfmisc_1(k3_xboole_0(A_208, B_210), A_209))=k2_zfmisc_1(A_208, A_209))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3094])).
% 11.47/4.50  tff(c_3421, plain, (k2_xboole_0(k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', '#skF_4')), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1314, c_3385])).
% 11.47/4.50  tff(c_22, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.47/4.50  tff(c_284, plain, (![A_84, B_85]: (k3_tarski(k2_tarski(A_84, B_85))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.47/4.50  tff(c_317, plain, (![B_88, A_89]: (k3_tarski(k2_tarski(B_88, A_89))=k2_xboole_0(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_22, c_284])).
% 11.47/4.50  tff(c_36, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.47/4.50  tff(c_323, plain, (![B_88, A_89]: (k2_xboole_0(B_88, A_89)=k2_xboole_0(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_317, c_36])).
% 11.47/4.50  tff(c_678, plain, (![C_115, A_116, B_117]: (k2_xboole_0(k2_zfmisc_1(C_115, A_116), k2_zfmisc_1(C_115, B_117))=k2_zfmisc_1(C_115, k2_xboole_0(A_116, B_117)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.47/4.50  tff(c_720, plain, (![C_115, B_117, A_116]: (k2_xboole_0(k2_zfmisc_1(C_115, B_117), k2_zfmisc_1(C_115, A_116))=k2_zfmisc_1(C_115, k2_xboole_0(A_116, B_117)))), inference(superposition, [status(thm), theory('equality')], [c_323, c_678])).
% 11.47/4.50  tff(c_11332, plain, (k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_4')))=k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3421, c_720])).
% 11.47/4.50  tff(c_11364, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_11332])).
% 11.47/4.50  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.47/4.50  tff(c_3533, plain, (![A_213, C_214, B_215, D_216]: (k5_xboole_0(k2_zfmisc_1(A_213, C_214), k2_zfmisc_1(k3_xboole_0(A_213, B_215), k3_xboole_0(C_214, D_216)))=k4_xboole_0(k2_zfmisc_1(A_213, C_214), k2_zfmisc_1(B_215, D_216)))), inference(superposition, [status(thm), theory('equality')], [c_1308, c_8])).
% 11.47/4.50  tff(c_3618, plain, (![A_1, C_214, D_216]: (k5_xboole_0(k2_zfmisc_1(A_1, C_214), k2_zfmisc_1(A_1, k3_xboole_0(C_214, D_216)))=k4_xboole_0(k2_zfmisc_1(A_1, C_214), k2_zfmisc_1(A_1, D_216)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3533])).
% 11.47/4.50  tff(c_3645, plain, (![A_1, C_214, D_216]: (k5_xboole_0(k2_zfmisc_1(A_1, C_214), k2_zfmisc_1(A_1, k3_xboole_0(C_214, D_216)))=k2_zfmisc_1(A_1, k4_xboole_0(C_214, D_216)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3618])).
% 11.47/4.50  tff(c_11392, plain, (k5_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11364, c_3645])).
% 11.47/4.50  tff(c_11479, plain, (k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_11392])).
% 11.47/4.50  tff(c_11580, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11479, c_38])).
% 11.47/4.50  tff(c_11603, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2264, c_11580])).
% 11.47/4.50  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.47/4.50  tff(c_313, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_299])).
% 11.47/4.50  tff(c_11613, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_11603, c_313])).
% 11.47/4.50  tff(c_11620, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11613, c_1314])).
% 11.47/4.50  tff(c_50, plain, (![A_56, C_58, B_57]: (k4_xboole_0(k2_zfmisc_1(A_56, C_58), k2_zfmisc_1(B_57, C_58))=k2_zfmisc_1(k4_xboole_0(A_56, B_57), C_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.47/4.50  tff(c_3621, plain, (![A_213, A_1, B_215]: (k5_xboole_0(k2_zfmisc_1(A_213, A_1), k2_zfmisc_1(k3_xboole_0(A_213, B_215), A_1))=k4_xboole_0(k2_zfmisc_1(A_213, A_1), k2_zfmisc_1(B_215, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3533])).
% 11.47/4.50  tff(c_3646, plain, (![A_213, A_1, B_215]: (k5_xboole_0(k2_zfmisc_1(A_213, A_1), k2_zfmisc_1(k3_xboole_0(A_213, B_215), A_1))=k2_zfmisc_1(k4_xboole_0(A_213, B_215), A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3621])).
% 11.47/4.50  tff(c_11729, plain, (k5_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11620, c_3646])).
% 11.47/4.50  tff(c_11819, plain, (k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_11729])).
% 11.47/4.50  tff(c_11919, plain, (k1_xboole_0='#skF_2' | k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11819, c_38])).
% 11.47/4.50  tff(c_11942, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_221, c_11919])).
% 11.47/4.50  tff(c_11969, plain, (![A_47]: (k2_zfmisc_1(A_47, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11942, c_11942, c_40])).
% 11.47/4.50  tff(c_11971, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11942, c_56])).
% 11.47/4.50  tff(c_12484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11969, c_11971])).
% 11.47/4.50  tff(c_12486, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 11.47/4.50  tff(c_12566, plain, (![A_3468, B_3469]: (k3_xboole_0(A_3468, B_3469)=A_3468 | ~r1_tarski(A_3468, B_3469))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.47/4.50  tff(c_12576, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_12486, c_12566])).
% 11.47/4.50  tff(c_13623, plain, (![A_3533, C_3534, B_3535, D_3536]: (k3_xboole_0(k2_zfmisc_1(A_3533, C_3534), k2_zfmisc_1(B_3535, D_3536))=k2_zfmisc_1(k3_xboole_0(A_3533, B_3535), k3_xboole_0(C_3534, D_3536)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.47/4.50  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.47/4.50  tff(c_12583, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_14])).
% 11.47/4.50  tff(c_13629, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13623, c_12583])).
% 11.47/4.50  tff(c_13702, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12576, c_13629])).
% 11.47/4.50  tff(c_13745, plain, (![A_56]: (k4_xboole_0(k2_zfmisc_1('#skF_1', A_56), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1('#skF_1', k4_xboole_0(A_56, k3_xboole_0('#skF_2', '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_13702, c_52])).
% 11.47/4.50  tff(c_16533, plain, (![A_3628]: (k2_zfmisc_1('#skF_1', k4_xboole_0(A_3628, k3_xboole_0('#skF_2', '#skF_4')))=k2_zfmisc_1('#skF_1', k4_xboole_0(A_3628, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_13745])).
% 11.47/4.50  tff(c_16625, plain, (![B_8]: (k2_zfmisc_1('#skF_1', k4_xboole_0(k3_xboole_0(k3_xboole_0('#skF_2', '#skF_4'), B_8), '#skF_2'))=k2_zfmisc_1('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12612, c_16533])).
% 11.47/4.50  tff(c_16648, plain, (![B_3629]: (k2_zfmisc_1('#skF_1', k4_xboole_0(k3_xboole_0(k3_xboole_0('#skF_2', '#skF_4'), B_3629), '#skF_2'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16625])).
% 11.47/4.50  tff(c_16758, plain, (![B_3629]: (k4_xboole_0(k3_xboole_0(k3_xboole_0('#skF_2', '#skF_4'), B_3629), '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16648, c_38])).
% 11.47/4.50  tff(c_16763, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_16758])).
% 11.47/4.50  tff(c_16802, plain, (![B_48]: (k2_zfmisc_1('#skF_1', B_48)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16763, c_16763, c_42])).
% 11.47/4.50  tff(c_16803, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16763, c_56])).
% 11.47/4.50  tff(c_16827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16802, c_16803])).
% 11.47/4.50  tff(c_16829, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_16758])).
% 11.47/4.50  tff(c_12667, plain, (![A_3479, B_3480]: (r1_tarski(A_3479, B_3480) | k4_xboole_0(A_3479, B_3480)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.47/4.50  tff(c_12485, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 11.47/4.50  tff(c_12683, plain, (k4_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_12667, c_12485])).
% 11.47/4.50  tff(c_16048, plain, (![A_3613, C_3614, B_3615, D_3616]: (k5_xboole_0(k2_zfmisc_1(A_3613, C_3614), k2_zfmisc_1(k3_xboole_0(A_3613, B_3615), k3_xboole_0(C_3614, D_3616)))=k4_xboole_0(k2_zfmisc_1(A_3613, C_3614), k2_zfmisc_1(B_3615, D_3616)))), inference(superposition, [status(thm), theory('equality')], [c_13623, c_8])).
% 11.47/4.50  tff(c_16130, plain, (![A_1, C_3614, D_3616]: (k5_xboole_0(k2_zfmisc_1(A_1, C_3614), k2_zfmisc_1(A_1, k3_xboole_0(C_3614, D_3616)))=k4_xboole_0(k2_zfmisc_1(A_1, C_3614), k2_zfmisc_1(A_1, D_3616)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_16048])).
% 11.47/4.50  tff(c_22107, plain, (![A_6721, C_6722, D_6723]: (k5_xboole_0(k2_zfmisc_1(A_6721, C_6722), k2_zfmisc_1(A_6721, k3_xboole_0(C_6722, D_6723)))=k2_zfmisc_1(A_6721, k4_xboole_0(C_6722, D_6723)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16130])).
% 11.47/4.50  tff(c_22197, plain, (k5_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13702, c_22107])).
% 11.47/4.50  tff(c_22265, plain, (k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22197])).
% 11.47/4.50  tff(c_22379, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_22265, c_38])).
% 11.47/4.50  tff(c_22414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16829, c_12683, c_22379])).
% 11.47/4.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.47/4.50  
% 11.47/4.50  Inference rules
% 11.47/4.50  ----------------------
% 11.47/4.50  #Ref     : 0
% 11.47/4.50  #Sup     : 5749
% 11.47/4.50  #Fact    : 0
% 11.47/4.50  #Define  : 0
% 11.47/4.50  #Split   : 7
% 11.47/4.50  #Chain   : 0
% 11.47/4.50  #Close   : 0
% 11.47/4.50  
% 11.47/4.50  Ordering : KBO
% 11.47/4.50  
% 11.47/4.50  Simplification rules
% 11.47/4.50  ----------------------
% 11.47/4.50  #Subsume      : 126
% 11.47/4.50  #Demod        : 5785
% 11.47/4.50  #Tautology    : 2414
% 11.47/4.50  #SimpNegUnit  : 48
% 11.47/4.50  #BackRed      : 182
% 11.47/4.50  
% 11.47/4.50  #Partial instantiations: 532
% 11.47/4.50  #Strategies tried      : 1
% 11.47/4.50  
% 11.47/4.50  Timing (in seconds)
% 11.47/4.50  ----------------------
% 11.47/4.50  Preprocessing        : 0.33
% 11.47/4.50  Parsing              : 0.18
% 11.47/4.50  CNF conversion       : 0.02
% 11.47/4.50  Main loop            : 3.39
% 11.47/4.50  Inferencing          : 0.76
% 11.47/4.50  Reduction            : 1.82
% 11.47/4.50  Demodulation         : 1.59
% 11.47/4.50  BG Simplification    : 0.12
% 11.47/4.50  Subsumption          : 0.52
% 11.47/4.50  Abstraction          : 0.17
% 11.47/4.50  MUC search           : 0.00
% 11.47/4.50  Cooper               : 0.00
% 11.47/4.50  Total                : 3.76
% 11.47/4.50  Index Insertion      : 0.00
% 11.47/4.50  Index Deletion       : 0.00
% 11.47/4.50  Index Matching       : 0.00
% 11.47/4.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
