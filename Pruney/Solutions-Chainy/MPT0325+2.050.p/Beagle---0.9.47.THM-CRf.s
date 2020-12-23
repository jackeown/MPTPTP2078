%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:27 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 163 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 270 expanded)
%              Number of equality atoms :   78 ( 140 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(c_1014,plain,(
    ! [A_116,B_117] :
      ( r1_tarski(A_116,B_117)
      | k4_xboole_0(A_116,B_117) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_57,plain,(
    k4_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_42])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [A_43,B_44] : k5_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_90])).

tff(c_102,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_99])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_129,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( ~ r1_xboole_0(A_52,B_53)
      | r1_xboole_0(k2_zfmisc_1(A_52,C_54),k2_zfmisc_1(B_53,D_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_172,plain,(
    ! [A_64,C_65,B_66,D_67] :
      ( k3_xboole_0(k2_zfmisc_1(A_64,C_65),k2_zfmisc_1(B_66,D_67)) = k1_xboole_0
      | ~ r1_xboole_0(A_64,B_66) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_34,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_14])).

tff(c_181,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_66])).

tff(c_196,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_181])).

tff(c_203,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_196])).

tff(c_110,plain,(
    ! [C_46,D_47,A_48,B_49] :
      ( ~ r1_xboole_0(C_46,D_47)
      | r1_xboole_0(k2_zfmisc_1(A_48,C_46),k2_zfmisc_1(B_49,D_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_143,plain,(
    ! [A_56,C_57,B_58,D_59] :
      ( k3_xboole_0(k2_zfmisc_1(A_56,C_57),k2_zfmisc_1(B_58,D_59)) = k1_xboole_0
      | ~ r1_xboole_0(C_57,D_59) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_149,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_66])).

tff(c_160,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_149])).

tff(c_166,plain,(
    k3_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_160])).

tff(c_211,plain,(
    ! [A_72,C_73,B_74,D_75] : k3_xboole_0(k2_zfmisc_1(A_72,C_73),k2_zfmisc_1(B_74,D_75)) = k2_zfmisc_1(k3_xboole_0(A_72,B_74),k3_xboole_0(C_73,D_75)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_217,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_66])).

tff(c_28,plain,(
    ! [C_25,A_23,B_24,D_26] :
      ( C_25 = A_23
      | k1_xboole_0 = B_24
      | k1_xboole_0 = A_23
      | k2_zfmisc_1(C_25,D_26) != k2_zfmisc_1(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_247,plain,(
    ! [C_25,D_26] :
      ( k3_xboole_0('#skF_1','#skF_3') = C_25
      | k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0
      | k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0
      | k2_zfmisc_1(C_25,D_26) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_28])).

tff(c_265,plain,(
    ! [C_25,D_26] :
      ( k3_xboole_0('#skF_1','#skF_3') = C_25
      | k2_zfmisc_1(C_25,D_26) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_166,c_247])).

tff(c_946,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_265])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_984,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_10])).

tff(c_987,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_984])).

tff(c_989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_987])).

tff(c_990,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1022,plain,(
    k4_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1014,c_990])).

tff(c_1055,plain,(
    ! [A_126,B_127] : k5_xboole_0(A_126,k3_xboole_0(A_126,B_127)) = k4_xboole_0(A_126,B_127) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1067,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1055])).

tff(c_1071,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1067])).

tff(c_991,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1033,plain,(
    ! [A_122,B_123] :
      ( k3_xboole_0(A_122,B_123) = A_122
      | ~ r1_tarski(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1045,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_991,c_1033])).

tff(c_1104,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( ~ r1_xboole_0(A_135,B_136)
      | r1_xboole_0(k2_zfmisc_1(A_135,C_137),k2_zfmisc_1(B_136,D_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1147,plain,(
    ! [A_147,C_148,B_149,D_150] :
      ( k3_xboole_0(k2_zfmisc_1(A_147,C_148),k2_zfmisc_1(B_149,D_150)) = k1_xboole_0
      | ~ r1_xboole_0(A_147,B_149) ) ),
    inference(resolution,[status(thm)],[c_1104,c_2])).

tff(c_1044,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1033])).

tff(c_1156,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1147,c_1044])).

tff(c_1171,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1156])).

tff(c_1177,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_1171])).

tff(c_1179,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_1177])).

tff(c_1099,plain,(
    ! [C_131,D_132,A_133,B_134] :
      ( ~ r1_xboole_0(C_131,D_132)
      | r1_xboole_0(k2_zfmisc_1(A_133,C_131),k2_zfmisc_1(B_134,D_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1123,plain,(
    ! [A_143,C_144,B_145,D_146] :
      ( k3_xboole_0(k2_zfmisc_1(A_143,C_144),k2_zfmisc_1(B_145,D_146)) = k1_xboole_0
      | ~ r1_xboole_0(C_144,D_146) ) ),
    inference(resolution,[status(thm)],[c_1099,c_2])).

tff(c_1129,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1123,c_1044])).

tff(c_1140,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1129])).

tff(c_1146,plain,(
    k3_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_1140])).

tff(c_1187,plain,(
    ! [A_155,C_156,B_157,D_158] : k3_xboole_0(k2_zfmisc_1(A_155,C_156),k2_zfmisc_1(B_157,D_158)) = k2_zfmisc_1(k3_xboole_0(A_155,B_157),k3_xboole_0(C_156,D_158)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1193,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1187,c_1044])).

tff(c_1204,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_1193])).

tff(c_26,plain,(
    ! [D_26,B_24,A_23,C_25] :
      ( D_26 = B_24
      | k1_xboole_0 = B_24
      | k1_xboole_0 = A_23
      | k2_zfmisc_1(C_25,D_26) != k2_zfmisc_1(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1219,plain,(
    ! [D_26,C_25] :
      ( k3_xboole_0('#skF_2','#skF_4') = D_26
      | k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1(C_25,D_26) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1204,c_26])).

tff(c_1242,plain,(
    ! [D_26,C_25] :
      ( k3_xboole_0('#skF_2','#skF_4') = D_26
      | k2_zfmisc_1(C_25,D_26) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1179,c_1146,c_1219])).

tff(c_1257,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1242])).

tff(c_1269,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_10])).

tff(c_1272,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_1269])).

tff(c_1274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1022,c_1272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:37:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  
% 3.20/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.20/1.50  
% 3.20/1.50  %Foreground sorts:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Background operators:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Foreground operators:
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.20/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.20/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.20/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.50  
% 3.36/1.51  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.36/1.51  tff(f_72, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 3.36/1.51  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.36/1.51  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.36/1.51  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.36/1.51  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.36/1.51  tff(f_53, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 3.36/1.51  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.36/1.51  tff(f_47, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 3.36/1.51  tff(f_63, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 3.36/1.51  tff(c_1014, plain, (![A_116, B_117]: (r1_tarski(A_116, B_117) | k4_xboole_0(A_116, B_117)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.51  tff(c_53, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.51  tff(c_30, plain, (~r1_tarski('#skF_2', '#skF_4') | ~r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.51  tff(c_42, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 3.36/1.51  tff(c_57, plain, (k4_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_42])).
% 3.36/1.51  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.51  tff(c_12, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.36/1.51  tff(c_90, plain, (![A_43, B_44]: (k5_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.51  tff(c_99, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k5_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_12, c_90])).
% 3.36/1.51  tff(c_102, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_99])).
% 3.36/1.51  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.51  tff(c_32, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.51  tff(c_129, plain, (![A_52, B_53, C_54, D_55]: (~r1_xboole_0(A_52, B_53) | r1_xboole_0(k2_zfmisc_1(A_52, C_54), k2_zfmisc_1(B_53, D_55)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.51  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.51  tff(c_172, plain, (![A_64, C_65, B_66, D_67]: (k3_xboole_0(k2_zfmisc_1(A_64, C_65), k2_zfmisc_1(B_66, D_67))=k1_xboole_0 | ~r1_xboole_0(A_64, B_66))), inference(resolution, [status(thm)], [c_129, c_2])).
% 3.36/1.51  tff(c_34, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.51  tff(c_14, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.36/1.51  tff(c_66, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_14])).
% 3.36/1.51  tff(c_181, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_172, c_66])).
% 3.36/1.51  tff(c_196, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_181])).
% 3.36/1.51  tff(c_203, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_196])).
% 3.36/1.51  tff(c_110, plain, (![C_46, D_47, A_48, B_49]: (~r1_xboole_0(C_46, D_47) | r1_xboole_0(k2_zfmisc_1(A_48, C_46), k2_zfmisc_1(B_49, D_47)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.51  tff(c_143, plain, (![A_56, C_57, B_58, D_59]: (k3_xboole_0(k2_zfmisc_1(A_56, C_57), k2_zfmisc_1(B_58, D_59))=k1_xboole_0 | ~r1_xboole_0(C_57, D_59))), inference(resolution, [status(thm)], [c_110, c_2])).
% 3.36/1.51  tff(c_149, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_143, c_66])).
% 3.36/1.51  tff(c_160, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_149])).
% 3.36/1.51  tff(c_166, plain, (k3_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_160])).
% 3.36/1.51  tff(c_211, plain, (![A_72, C_73, B_74, D_75]: (k3_xboole_0(k2_zfmisc_1(A_72, C_73), k2_zfmisc_1(B_74, D_75))=k2_zfmisc_1(k3_xboole_0(A_72, B_74), k3_xboole_0(C_73, D_75)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.51  tff(c_217, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_211, c_66])).
% 3.36/1.51  tff(c_28, plain, (![C_25, A_23, B_24, D_26]: (C_25=A_23 | k1_xboole_0=B_24 | k1_xboole_0=A_23 | k2_zfmisc_1(C_25, D_26)!=k2_zfmisc_1(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.51  tff(c_247, plain, (![C_25, D_26]: (k3_xboole_0('#skF_1', '#skF_3')=C_25 | k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0 | k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0 | k2_zfmisc_1(C_25, D_26)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_217, c_28])).
% 3.36/1.51  tff(c_265, plain, (![C_25, D_26]: (k3_xboole_0('#skF_1', '#skF_3')=C_25 | k2_zfmisc_1(C_25, D_26)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_203, c_166, c_247])).
% 3.36/1.51  tff(c_946, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_265])).
% 3.36/1.51  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.51  tff(c_984, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_946, c_10])).
% 3.36/1.51  tff(c_987, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_102, c_984])).
% 3.36/1.51  tff(c_989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_987])).
% 3.36/1.51  tff(c_990, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 3.36/1.51  tff(c_1022, plain, (k4_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1014, c_990])).
% 3.36/1.51  tff(c_1055, plain, (![A_126, B_127]: (k5_xboole_0(A_126, k3_xboole_0(A_126, B_127))=k4_xboole_0(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.51  tff(c_1067, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k5_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1055])).
% 3.36/1.51  tff(c_1071, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1067])).
% 3.36/1.51  tff(c_991, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 3.36/1.51  tff(c_1033, plain, (![A_122, B_123]: (k3_xboole_0(A_122, B_123)=A_122 | ~r1_tarski(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.36/1.51  tff(c_1045, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_991, c_1033])).
% 3.36/1.51  tff(c_1104, plain, (![A_135, B_136, C_137, D_138]: (~r1_xboole_0(A_135, B_136) | r1_xboole_0(k2_zfmisc_1(A_135, C_137), k2_zfmisc_1(B_136, D_138)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.51  tff(c_1147, plain, (![A_147, C_148, B_149, D_150]: (k3_xboole_0(k2_zfmisc_1(A_147, C_148), k2_zfmisc_1(B_149, D_150))=k1_xboole_0 | ~r1_xboole_0(A_147, B_149))), inference(resolution, [status(thm)], [c_1104, c_2])).
% 3.36/1.51  tff(c_1044, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_1033])).
% 3.36/1.51  tff(c_1156, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1147, c_1044])).
% 3.36/1.51  tff(c_1171, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_1156])).
% 3.36/1.51  tff(c_1177, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_1171])).
% 3.36/1.51  tff(c_1179, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_1177])).
% 3.36/1.51  tff(c_1099, plain, (![C_131, D_132, A_133, B_134]: (~r1_xboole_0(C_131, D_132) | r1_xboole_0(k2_zfmisc_1(A_133, C_131), k2_zfmisc_1(B_134, D_132)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.51  tff(c_1123, plain, (![A_143, C_144, B_145, D_146]: (k3_xboole_0(k2_zfmisc_1(A_143, C_144), k2_zfmisc_1(B_145, D_146))=k1_xboole_0 | ~r1_xboole_0(C_144, D_146))), inference(resolution, [status(thm)], [c_1099, c_2])).
% 3.36/1.51  tff(c_1129, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1123, c_1044])).
% 3.36/1.51  tff(c_1140, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_1129])).
% 3.36/1.51  tff(c_1146, plain, (k3_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_1140])).
% 3.36/1.51  tff(c_1187, plain, (![A_155, C_156, B_157, D_158]: (k3_xboole_0(k2_zfmisc_1(A_155, C_156), k2_zfmisc_1(B_157, D_158))=k2_zfmisc_1(k3_xboole_0(A_155, B_157), k3_xboole_0(C_156, D_158)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.51  tff(c_1193, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1187, c_1044])).
% 3.36/1.51  tff(c_1204, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_1193])).
% 3.36/1.51  tff(c_26, plain, (![D_26, B_24, A_23, C_25]: (D_26=B_24 | k1_xboole_0=B_24 | k1_xboole_0=A_23 | k2_zfmisc_1(C_25, D_26)!=k2_zfmisc_1(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.51  tff(c_1219, plain, (![D_26, C_25]: (k3_xboole_0('#skF_2', '#skF_4')=D_26 | k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_1' | k2_zfmisc_1(C_25, D_26)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1204, c_26])).
% 3.36/1.51  tff(c_1242, plain, (![D_26, C_25]: (k3_xboole_0('#skF_2', '#skF_4')=D_26 | k2_zfmisc_1(C_25, D_26)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1179, c_1146, c_1219])).
% 3.36/1.51  tff(c_1257, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_1242])).
% 3.36/1.51  tff(c_1269, plain, (k5_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1257, c_10])).
% 3.36/1.51  tff(c_1272, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_1269])).
% 3.36/1.51  tff(c_1274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1022, c_1272])).
% 3.36/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.51  
% 3.36/1.51  Inference rules
% 3.36/1.51  ----------------------
% 3.36/1.51  #Ref     : 9
% 3.36/1.51  #Sup     : 340
% 3.36/1.51  #Fact    : 0
% 3.36/1.51  #Define  : 0
% 3.36/1.51  #Split   : 3
% 3.36/1.51  #Chain   : 0
% 3.36/1.51  #Close   : 0
% 3.36/1.51  
% 3.36/1.51  Ordering : KBO
% 3.36/1.51  
% 3.36/1.51  Simplification rules
% 3.36/1.51  ----------------------
% 3.36/1.51  #Subsume      : 68
% 3.36/1.51  #Demod        : 44
% 3.36/1.51  #Tautology    : 120
% 3.36/1.51  #SimpNegUnit  : 26
% 3.36/1.51  #BackRed      : 11
% 3.36/1.51  
% 3.36/1.51  #Partial instantiations: 0
% 3.36/1.51  #Strategies tried      : 1
% 3.36/1.51  
% 3.36/1.51  Timing (in seconds)
% 3.36/1.51  ----------------------
% 3.36/1.52  Preprocessing        : 0.30
% 3.36/1.52  Parsing              : 0.16
% 3.36/1.52  CNF conversion       : 0.02
% 3.36/1.52  Main loop            : 0.43
% 3.36/1.52  Inferencing          : 0.16
% 3.36/1.52  Reduction            : 0.12
% 3.36/1.52  Demodulation         : 0.08
% 3.36/1.52  BG Simplification    : 0.02
% 3.36/1.52  Subsumption          : 0.09
% 3.36/1.52  Abstraction          : 0.03
% 3.36/1.52  MUC search           : 0.00
% 3.36/1.52  Cooper               : 0.00
% 3.36/1.52  Total                : 0.77
% 3.36/1.52  Index Insertion      : 0.00
% 3.36/1.52  Index Deletion       : 0.00
% 3.36/1.52  Index Matching       : 0.00
% 3.36/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
