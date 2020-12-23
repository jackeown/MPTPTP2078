%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:11 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 322 expanded)
%              Number of leaves         :   31 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 402 expanded)
%              Number of equality atoms :   71 ( 232 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( A != B
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),D))
          & r1_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(D,k1_tarski(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3023,plain,(
    ! [A_183,B_184] : k5_xboole_0(A_183,k3_xboole_0(A_183,B_184)) = k4_xboole_0(A_183,B_184) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3047,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3023])).

tff(c_89,plain,(
    ! [A_36,B_37] : r1_xboole_0(k3_xboole_0(A_36,B_37),k5_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_95,plain,(
    ! [A_3] : r1_xboole_0(A_3,k5_xboole_0(A_3,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_89])).

tff(c_2933,plain,(
    ! [A_173,B_174] :
      ( k4_xboole_0(A_173,B_174) = A_173
      | ~ r1_xboole_0(A_173,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2947,plain,(
    ! [A_3] : k4_xboole_0(A_3,k5_xboole_0(A_3,A_3)) = A_3 ),
    inference(resolution,[status(thm)],[c_95,c_2933])).

tff(c_3332,plain,(
    ! [A_3] : k4_xboole_0(A_3,k4_xboole_0(A_3,A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3047,c_2947])).

tff(c_18,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3044,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3023])).

tff(c_3052,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3044])).

tff(c_2870,plain,(
    ! [A_164,B_165] : r1_tarski(k4_xboole_0(A_164,B_165),k5_xboole_0(A_164,B_165)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2873,plain,(
    ! [A_13] : r1_tarski(A_13,k5_xboole_0(A_13,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2870])).

tff(c_3057,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3052,c_2873])).

tff(c_3213,plain,(
    ! [A_193,B_194,C_195] :
      ( r1_tarski(A_193,B_194)
      | ~ r1_tarski(A_193,k4_xboole_0(B_194,C_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3232,plain,(
    ! [B_196,C_197] : r1_tarski(k4_xboole_0(B_196,C_197),B_196) ),
    inference(resolution,[status(thm)],[c_3057,c_3213])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_xboole_0(A_9,C_11)
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3616,plain,(
    ! [B_215,C_216,C_217] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_215,C_216),C_217),C_216) ),
    inference(resolution,[status(thm)],[c_3232,c_12])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5256,plain,(
    ! [B_274,C_275,C_276] : k3_xboole_0(k4_xboole_0(k4_xboole_0(B_274,C_275),C_276),C_275) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3616,c_2])).

tff(c_5328,plain,(
    ! [A_3,C_276] : k3_xboole_0(k4_xboole_0(A_3,C_276),k4_xboole_0(A_3,A_3)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3332,c_5256])).

tff(c_32,plain,(
    ! [A_23,C_25,B_24,D_26] : k3_xboole_0(k2_zfmisc_1(A_23,C_25),k2_zfmisc_1(B_24,D_26)) = k2_zfmisc_1(k3_xboole_0(A_23,B_24),k3_xboole_0(C_25,D_26)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    ! [C_29,A_27,B_28] : k4_xboole_0(k2_zfmisc_1(C_29,A_27),k2_zfmisc_1(C_29,B_28)) = k2_zfmisc_1(C_29,k4_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5737,plain,(
    ! [A_285,C_286] : k3_xboole_0(k4_xboole_0(A_285,C_286),k4_xboole_0(A_285,A_285)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3332,c_5256])).

tff(c_5801,plain,(
    ! [C_29,A_27,B_28] : k3_xboole_0(k2_zfmisc_1(C_29,k4_xboole_0(A_27,B_28)),k4_xboole_0(k2_zfmisc_1(C_29,A_27),k2_zfmisc_1(C_29,A_27))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5737])).

tff(c_5857,plain,(
    ! [C_29] : k2_zfmisc_1(C_29,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5328,c_6,c_32,c_36,c_5801])).

tff(c_44,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(k1_tarski(A_30),k1_tarski(B_31)) = k1_tarski(A_30)
      | B_31 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2888,plain,(
    ! [A_169,B_170] :
      ( k3_xboole_0(A_169,B_170) = k1_xboole_0
      | ~ r1_xboole_0(A_169,B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4024,plain,(
    ! [A_240,B_241] :
      ( k3_xboole_0(A_240,B_241) = k1_xboole_0
      | k4_xboole_0(A_240,B_241) != A_240 ) ),
    inference(resolution,[status(thm)],[c_22,c_2888])).

tff(c_4506,plain,(
    ! [A_255,B_256] :
      ( k3_xboole_0(k1_tarski(A_255),k1_tarski(B_256)) = k1_xboole_0
      | B_256 = A_255 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4024])).

tff(c_2950,plain,(
    ! [A_175,B_176] :
      ( r1_xboole_0(A_175,B_176)
      | k3_xboole_0(A_175,B_176) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_245,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_269,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_245])).

tff(c_571,plain,(
    ! [A_83] : r1_xboole_0(A_83,k4_xboole_0(A_83,A_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_95])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_591,plain,(
    ! [A_83] : k4_xboole_0(A_83,k4_xboole_0(A_83,A_83)) = A_83 ),
    inference(resolution,[status(thm)],[c_571,c_20])).

tff(c_266,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_245])).

tff(c_274,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_266])).

tff(c_101,plain,(
    ! [A_43,B_44] : r1_tarski(k4_xboole_0(A_43,B_44),k5_xboole_0(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_104,plain,(
    ! [A_13] : r1_tarski(A_13,k5_xboole_0(A_13,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_101])).

tff(c_279,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_104])).

tff(c_402,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(A_68,B_69)
      | ~ r1_tarski(A_68,k4_xboole_0(B_69,C_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_416,plain,(
    ! [B_69,C_70] : r1_tarski(k4_xboole_0(B_69,C_70),B_69) ),
    inference(resolution,[status(thm)],[c_279,c_402])).

tff(c_452,plain,(
    ! [A_74,C_75,B_76] :
      ( r1_xboole_0(A_74,C_75)
      | ~ r1_tarski(A_74,k4_xboole_0(B_76,C_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_832,plain,(
    ! [B_96,C_97,C_98] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_96,C_97),C_98),C_97) ),
    inference(resolution,[status(thm)],[c_416,c_452])).

tff(c_2196,plain,(
    ! [B_147,C_148,C_149] : k3_xboole_0(k4_xboole_0(k4_xboole_0(B_147,C_148),C_149),C_148) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_832,c_2])).

tff(c_2265,plain,(
    ! [A_83,C_149] : k3_xboole_0(k4_xboole_0(A_83,C_149),k4_xboole_0(A_83,A_83)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_2196])).

tff(c_2480,plain,(
    ! [A_157,C_158] : k3_xboole_0(k4_xboole_0(A_157,C_158),k4_xboole_0(A_157,A_157)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_2196])).

tff(c_2553,plain,(
    ! [C_29,A_27,B_28] : k3_xboole_0(k2_zfmisc_1(C_29,k4_xboole_0(A_27,B_28)),k4_xboole_0(k2_zfmisc_1(C_29,A_27),k2_zfmisc_1(C_29,A_27))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2480])).

tff(c_2606,plain,(
    ! [C_29] : k2_zfmisc_1(C_29,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2265,c_6,c_32,c_36,c_2553])).

tff(c_2516,plain,(
    ! [A_157] : k4_xboole_0(A_157,A_157) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2480,c_6])).

tff(c_890,plain,(
    ! [A_100,C_101,B_102] : k4_xboole_0(k2_zfmisc_1(A_100,C_101),k2_zfmisc_1(B_102,C_101)) = k2_zfmisc_1(k4_xboole_0(A_100,B_102),C_101) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_907,plain,(
    ! [B_102,C_101] : k2_zfmisc_1(k4_xboole_0(B_102,B_102),C_101) = k2_zfmisc_1(B_102,k4_xboole_0(C_101,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_36])).

tff(c_2863,plain,(
    ! [C_101] : k2_zfmisc_1(k1_xboole_0,C_101) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2606,c_2516,c_2516,c_907])).

tff(c_169,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = k1_xboole_0
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1186,plain,(
    ! [A_121,B_122] :
      ( k3_xboole_0(A_121,B_122) = k1_xboole_0
      | k4_xboole_0(A_121,B_122) != A_121 ) ),
    inference(resolution,[status(thm)],[c_22,c_169])).

tff(c_1673,plain,(
    ! [A_133,B_134] :
      ( k3_xboole_0(k1_tarski(A_133),k1_tarski(B_134)) = k1_xboole_0
      | B_134 = A_133 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1186])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_4',k1_tarski('#skF_2')))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_3'),k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_99,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_3'),k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_196,plain,(
    k3_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_3'),k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_99])).

tff(c_993,plain,(
    k2_zfmisc_1(k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')),k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_196])).

tff(c_1682,plain,
    ( k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1673,c_993])).

tff(c_1705,plain,(
    k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1682])).

tff(c_2866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2863,c_1705])).

tff(c_2867,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_4',k1_tarski('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2962,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_4',k1_tarski('#skF_2'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2950,c_2867])).

tff(c_4430,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_4'),k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2962])).

tff(c_4512,plain,
    ( k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_4'),k1_xboole_0) != k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4506,c_4430])).

tff(c_4534,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_4'),k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_4512])).

tff(c_6232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5857,c_4534])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:04:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.92  
% 4.63/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.92  %$ r1_xboole_0 > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.63/1.92  
% 4.63/1.92  %Foreground sorts:
% 4.63/1.92  
% 4.63/1.92  
% 4.63/1.92  %Background operators:
% 4.63/1.92  
% 4.63/1.92  
% 4.63/1.92  %Foreground operators:
% 4.63/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.63/1.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.63/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.63/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.63/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.63/1.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.63/1.92  tff('#skF_2', type, '#skF_2': $i).
% 4.63/1.92  tff('#skF_3', type, '#skF_3': $i).
% 4.63/1.92  tff('#skF_1', type, '#skF_1': $i).
% 4.63/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.63/1.92  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.63/1.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.63/1.92  
% 4.97/1.94  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.97/1.94  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.97/1.94  tff(f_33, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 4.97/1.94  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.97/1.94  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.97/1.94  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.97/1.94  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 4.97/1.94  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.97/1.94  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.97/1.94  tff(f_59, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 4.97/1.94  tff(f_63, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 4.97/1.94  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (~(A = B) => (r1_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), D)) & r1_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(D, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_zfmisc_1)).
% 4.97/1.94  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.97/1.94  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.97/1.94  tff(c_3023, plain, (![A_183, B_184]: (k5_xboole_0(A_183, k3_xboole_0(A_183, B_184))=k4_xboole_0(A_183, B_184))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.97/1.94  tff(c_3047, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_3023])).
% 4.97/1.94  tff(c_89, plain, (![A_36, B_37]: (r1_xboole_0(k3_xboole_0(A_36, B_37), k5_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.97/1.94  tff(c_95, plain, (![A_3]: (r1_xboole_0(A_3, k5_xboole_0(A_3, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_89])).
% 4.97/1.94  tff(c_2933, plain, (![A_173, B_174]: (k4_xboole_0(A_173, B_174)=A_173 | ~r1_xboole_0(A_173, B_174))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.97/1.94  tff(c_2947, plain, (![A_3]: (k4_xboole_0(A_3, k5_xboole_0(A_3, A_3))=A_3)), inference(resolution, [status(thm)], [c_95, c_2933])).
% 4.97/1.94  tff(c_3332, plain, (![A_3]: (k4_xboole_0(A_3, k4_xboole_0(A_3, A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_3047, c_2947])).
% 4.97/1.94  tff(c_18, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.97/1.94  tff(c_16, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.97/1.94  tff(c_3044, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3023])).
% 4.97/1.94  tff(c_3052, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3044])).
% 4.97/1.94  tff(c_2870, plain, (![A_164, B_165]: (r1_tarski(k4_xboole_0(A_164, B_165), k5_xboole_0(A_164, B_165)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.97/1.94  tff(c_2873, plain, (![A_13]: (r1_tarski(A_13, k5_xboole_0(A_13, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2870])).
% 4.97/1.94  tff(c_3057, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_3052, c_2873])).
% 4.97/1.94  tff(c_3213, plain, (![A_193, B_194, C_195]: (r1_tarski(A_193, B_194) | ~r1_tarski(A_193, k4_xboole_0(B_194, C_195)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.97/1.94  tff(c_3232, plain, (![B_196, C_197]: (r1_tarski(k4_xboole_0(B_196, C_197), B_196))), inference(resolution, [status(thm)], [c_3057, c_3213])).
% 4.97/1.94  tff(c_12, plain, (![A_9, C_11, B_10]: (r1_xboole_0(A_9, C_11) | ~r1_tarski(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.97/1.94  tff(c_3616, plain, (![B_215, C_216, C_217]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_215, C_216), C_217), C_216))), inference(resolution, [status(thm)], [c_3232, c_12])).
% 4.97/1.94  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.97/1.94  tff(c_5256, plain, (![B_274, C_275, C_276]: (k3_xboole_0(k4_xboole_0(k4_xboole_0(B_274, C_275), C_276), C_275)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3616, c_2])).
% 4.97/1.94  tff(c_5328, plain, (![A_3, C_276]: (k3_xboole_0(k4_xboole_0(A_3, C_276), k4_xboole_0(A_3, A_3))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3332, c_5256])).
% 4.97/1.94  tff(c_32, plain, (![A_23, C_25, B_24, D_26]: (k3_xboole_0(k2_zfmisc_1(A_23, C_25), k2_zfmisc_1(B_24, D_26))=k2_zfmisc_1(k3_xboole_0(A_23, B_24), k3_xboole_0(C_25, D_26)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.97/1.94  tff(c_36, plain, (![C_29, A_27, B_28]: (k4_xboole_0(k2_zfmisc_1(C_29, A_27), k2_zfmisc_1(C_29, B_28))=k2_zfmisc_1(C_29, k4_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.97/1.94  tff(c_5737, plain, (![A_285, C_286]: (k3_xboole_0(k4_xboole_0(A_285, C_286), k4_xboole_0(A_285, A_285))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3332, c_5256])).
% 4.97/1.94  tff(c_5801, plain, (![C_29, A_27, B_28]: (k3_xboole_0(k2_zfmisc_1(C_29, k4_xboole_0(A_27, B_28)), k4_xboole_0(k2_zfmisc_1(C_29, A_27), k2_zfmisc_1(C_29, A_27)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_5737])).
% 4.97/1.94  tff(c_5857, plain, (![C_29]: (k2_zfmisc_1(C_29, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5328, c_6, c_32, c_36, c_5801])).
% 4.97/1.94  tff(c_44, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.97/1.94  tff(c_40, plain, (![A_30, B_31]: (k4_xboole_0(k1_tarski(A_30), k1_tarski(B_31))=k1_tarski(A_30) | B_31=A_30)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.97/1.94  tff(c_22, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.97/1.94  tff(c_2888, plain, (![A_169, B_170]: (k3_xboole_0(A_169, B_170)=k1_xboole_0 | ~r1_xboole_0(A_169, B_170))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.97/1.94  tff(c_4024, plain, (![A_240, B_241]: (k3_xboole_0(A_240, B_241)=k1_xboole_0 | k4_xboole_0(A_240, B_241)!=A_240)), inference(resolution, [status(thm)], [c_22, c_2888])).
% 4.97/1.94  tff(c_4506, plain, (![A_255, B_256]: (k3_xboole_0(k1_tarski(A_255), k1_tarski(B_256))=k1_xboole_0 | B_256=A_255)), inference(superposition, [status(thm), theory('equality')], [c_40, c_4024])).
% 4.97/1.94  tff(c_2950, plain, (![A_175, B_176]: (r1_xboole_0(A_175, B_176) | k3_xboole_0(A_175, B_176)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.97/1.94  tff(c_245, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.97/1.94  tff(c_269, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_245])).
% 4.97/1.94  tff(c_571, plain, (![A_83]: (r1_xboole_0(A_83, k4_xboole_0(A_83, A_83)))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_95])).
% 4.97/1.94  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.97/1.94  tff(c_591, plain, (![A_83]: (k4_xboole_0(A_83, k4_xboole_0(A_83, A_83))=A_83)), inference(resolution, [status(thm)], [c_571, c_20])).
% 4.97/1.94  tff(c_266, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_245])).
% 4.97/1.94  tff(c_274, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_266])).
% 4.97/1.94  tff(c_101, plain, (![A_43, B_44]: (r1_tarski(k4_xboole_0(A_43, B_44), k5_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.97/1.94  tff(c_104, plain, (![A_13]: (r1_tarski(A_13, k5_xboole_0(A_13, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_101])).
% 4.97/1.94  tff(c_279, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_104])).
% 4.97/1.94  tff(c_402, plain, (![A_68, B_69, C_70]: (r1_tarski(A_68, B_69) | ~r1_tarski(A_68, k4_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.97/1.94  tff(c_416, plain, (![B_69, C_70]: (r1_tarski(k4_xboole_0(B_69, C_70), B_69))), inference(resolution, [status(thm)], [c_279, c_402])).
% 4.97/1.94  tff(c_452, plain, (![A_74, C_75, B_76]: (r1_xboole_0(A_74, C_75) | ~r1_tarski(A_74, k4_xboole_0(B_76, C_75)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.97/1.94  tff(c_832, plain, (![B_96, C_97, C_98]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_96, C_97), C_98), C_97))), inference(resolution, [status(thm)], [c_416, c_452])).
% 4.97/1.94  tff(c_2196, plain, (![B_147, C_148, C_149]: (k3_xboole_0(k4_xboole_0(k4_xboole_0(B_147, C_148), C_149), C_148)=k1_xboole_0)), inference(resolution, [status(thm)], [c_832, c_2])).
% 4.97/1.94  tff(c_2265, plain, (![A_83, C_149]: (k3_xboole_0(k4_xboole_0(A_83, C_149), k4_xboole_0(A_83, A_83))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_591, c_2196])).
% 4.97/1.94  tff(c_2480, plain, (![A_157, C_158]: (k3_xboole_0(k4_xboole_0(A_157, C_158), k4_xboole_0(A_157, A_157))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_591, c_2196])).
% 4.97/1.94  tff(c_2553, plain, (![C_29, A_27, B_28]: (k3_xboole_0(k2_zfmisc_1(C_29, k4_xboole_0(A_27, B_28)), k4_xboole_0(k2_zfmisc_1(C_29, A_27), k2_zfmisc_1(C_29, A_27)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_2480])).
% 4.97/1.94  tff(c_2606, plain, (![C_29]: (k2_zfmisc_1(C_29, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2265, c_6, c_32, c_36, c_2553])).
% 4.97/1.94  tff(c_2516, plain, (![A_157]: (k4_xboole_0(A_157, A_157)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2480, c_6])).
% 4.97/1.94  tff(c_890, plain, (![A_100, C_101, B_102]: (k4_xboole_0(k2_zfmisc_1(A_100, C_101), k2_zfmisc_1(B_102, C_101))=k2_zfmisc_1(k4_xboole_0(A_100, B_102), C_101))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.97/1.94  tff(c_907, plain, (![B_102, C_101]: (k2_zfmisc_1(k4_xboole_0(B_102, B_102), C_101)=k2_zfmisc_1(B_102, k4_xboole_0(C_101, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_890, c_36])).
% 4.97/1.94  tff(c_2863, plain, (![C_101]: (k2_zfmisc_1(k1_xboole_0, C_101)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2606, c_2516, c_2516, c_907])).
% 4.97/1.94  tff(c_169, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=k1_xboole_0 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.97/1.94  tff(c_1186, plain, (![A_121, B_122]: (k3_xboole_0(A_121, B_122)=k1_xboole_0 | k4_xboole_0(A_121, B_122)!=A_121)), inference(resolution, [status(thm)], [c_22, c_169])).
% 4.97/1.94  tff(c_1673, plain, (![A_133, B_134]: (k3_xboole_0(k1_tarski(A_133), k1_tarski(B_134))=k1_xboole_0 | B_134=A_133)), inference(superposition, [status(thm), theory('equality')], [c_40, c_1186])).
% 4.97/1.94  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.97/1.94  tff(c_42, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_4', k1_tarski('#skF_2'))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.97/1.94  tff(c_99, plain, (~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_42])).
% 4.97/1.94  tff(c_196, plain, (k3_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_99])).
% 4.97/1.94  tff(c_993, plain, (k2_zfmisc_1(k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')), k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_196])).
% 4.97/1.94  tff(c_1682, plain, (k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1673, c_993])).
% 4.97/1.94  tff(c_1705, plain, (k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_1682])).
% 4.97/1.94  tff(c_2866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2863, c_1705])).
% 4.97/1.94  tff(c_2867, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_4', k1_tarski('#skF_2')))), inference(splitRight, [status(thm)], [c_42])).
% 4.97/1.94  tff(c_2962, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_4', k1_tarski('#skF_2')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_2950, c_2867])).
% 4.97/1.94  tff(c_4430, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_4'), k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2962])).
% 4.97/1.94  tff(c_4512, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)!=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4506, c_4430])).
% 4.97/1.94  tff(c_4534, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_4512])).
% 4.97/1.94  tff(c_6232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5857, c_4534])).
% 4.97/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/1.94  
% 4.97/1.94  Inference rules
% 4.97/1.94  ----------------------
% 4.97/1.94  #Ref     : 0
% 4.97/1.94  #Sup     : 1464
% 4.97/1.94  #Fact    : 0
% 4.97/1.94  #Define  : 0
% 4.97/1.94  #Split   : 3
% 4.97/1.94  #Chain   : 0
% 4.97/1.94  #Close   : 0
% 4.97/1.94  
% 4.97/1.94  Ordering : KBO
% 4.97/1.94  
% 4.97/1.94  Simplification rules
% 4.97/1.94  ----------------------
% 4.97/1.94  #Subsume      : 77
% 4.97/1.94  #Demod        : 1159
% 4.97/1.94  #Tautology    : 950
% 4.97/1.94  #SimpNegUnit  : 13
% 4.97/1.94  #BackRed      : 47
% 4.97/1.94  
% 4.97/1.94  #Partial instantiations: 0
% 4.97/1.94  #Strategies tried      : 1
% 4.97/1.94  
% 4.97/1.94  Timing (in seconds)
% 4.97/1.94  ----------------------
% 4.97/1.94  Preprocessing        : 0.30
% 4.97/1.94  Parsing              : 0.16
% 4.97/1.94  CNF conversion       : 0.02
% 4.97/1.94  Main loop            : 0.86
% 4.97/1.94  Inferencing          : 0.29
% 4.97/1.94  Reduction            : 0.33
% 4.97/1.94  Demodulation         : 0.25
% 4.97/1.94  BG Simplification    : 0.03
% 4.97/1.94  Subsumption          : 0.14
% 4.97/1.94  Abstraction          : 0.04
% 4.97/1.94  MUC search           : 0.00
% 4.97/1.94  Cooper               : 0.00
% 4.97/1.94  Total                : 1.20
% 4.97/1.94  Index Insertion      : 0.00
% 4.97/1.94  Index Deletion       : 0.00
% 4.97/1.94  Index Matching       : 0.00
% 4.97/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
