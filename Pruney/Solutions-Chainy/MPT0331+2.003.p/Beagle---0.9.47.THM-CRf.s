%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:45 EST 2020

% Result     : Theorem 44.18s
% Output     : CNFRefutation 44.18s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 186 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  100 ( 257 expanded)
%              Number of equality atoms :   56 ( 152 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(c_48,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_89,plain,(
    ! [A_39,B_38] : r1_tarski(A_39,k2_xboole_0(B_38,A_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_24])).

tff(c_557,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(k4_xboole_0(A_72,B_73),C_74)
      | ~ r1_tarski(A_72,k2_xboole_0(B_73,C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3955,plain,(
    ! [A_152,B_153,C_154] :
      ( k2_xboole_0(k4_xboole_0(A_152,B_153),C_154) = C_154
      | ~ r1_tarski(A_152,k2_xboole_0(B_153,C_154)) ) ),
    inference(resolution,[status(thm)],[c_557,c_10])).

tff(c_4041,plain,(
    ! [A_155,B_156] : k2_xboole_0(k4_xboole_0(A_155,B_156),A_155) = A_155 ),
    inference(resolution,[status(thm)],[c_89,c_3955])).

tff(c_4674,plain,(
    ! [A_166,B_167] : k2_xboole_0(k3_xboole_0(A_166,B_167),A_166) = A_166 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4041])).

tff(c_4801,plain,(
    ! [A_1,B_167] : k2_xboole_0(A_1,k3_xboole_0(A_1,B_167)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4674])).

tff(c_32,plain,(
    ! [B_26] : k2_zfmisc_1(k1_xboole_0,B_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1003,plain,(
    ! [C_95,A_96,B_97] : k4_xboole_0(k2_zfmisc_1(C_95,A_96),k2_zfmisc_1(C_95,B_97)) = k2_zfmisc_1(C_95,k4_xboole_0(A_96,B_97)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1052,plain,(
    ! [B_97,B_26] : k4_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,B_97)) = k2_zfmisc_1(k1_xboole_0,k4_xboole_0(B_26,B_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1003])).

tff(c_1060,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_1052])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(k4_xboole_0(A_11,B_12),C_13)
      | ~ r1_tarski(A_11,k2_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1071,plain,(
    ! [C_13] :
      ( r1_tarski(k1_xboole_0,C_13)
      | ~ r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,C_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_16])).

tff(c_1107,plain,(
    ! [C_98] : r1_tarski(k1_xboole_0,C_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1071])).

tff(c_1114,plain,(
    ! [C_98] : k2_xboole_0(k1_xboole_0,C_98) = C_98 ),
    inference(resolution,[status(thm)],[c_1107,c_10])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1212,plain,(
    ! [C_102] : k2_xboole_0(k1_xboole_0,C_102) = C_102 ),
    inference(resolution,[status(thm)],[c_1107,c_10])).

tff(c_1298,plain,(
    ! [B_8] : k4_xboole_0(B_8,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1212])).

tff(c_1329,plain,(
    ! [B_8] : k4_xboole_0(B_8,k1_xboole_0) = B_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_1298])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k3_xboole_0(A_18,B_19),C_20) = k3_xboole_0(A_18,k4_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_207,plain,(
    ! [A_53,B_54] : k2_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_213,plain,(
    ! [B_54,A_53] : r1_tarski(k4_xboole_0(B_54,A_53),k2_xboole_0(A_53,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_89])).

tff(c_4115,plain,(
    ! [A_155,B_156] : r1_tarski(k4_xboole_0(A_155,k4_xboole_0(A_155,B_156)),A_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_4041,c_213])).

tff(c_4227,plain,(
    ! [A_157,B_158] : r1_tarski(k3_xboole_0(A_157,B_158),A_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4115])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_122,plain,(
    ! [A_42,B_43] :
      ( k2_xboole_0(A_42,B_43) = B_43
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_122])).

tff(c_267,plain,(
    ! [A_58,B_59] : k4_xboole_0(k2_xboole_0(A_58,B_59),B_59) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_276,plain,(
    ! [B_59,A_58] : k2_xboole_0(B_59,k4_xboole_0(A_58,B_59)) = k2_xboole_0(B_59,k2_xboole_0(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_12])).

tff(c_296,plain,(
    ! [B_59,A_58] : k2_xboole_0(B_59,k2_xboole_0(A_58,B_59)) = k2_xboole_0(B_59,A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_276])).

tff(c_1224,plain,(
    ! [C_102] : k2_xboole_0(C_102,k1_xboole_0) = k2_xboole_0(C_102,C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_1212,c_296])).

tff(c_1313,plain,(
    ! [C_102] : k2_xboole_0(C_102,k1_xboole_0) = C_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_1224])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1625,plain,(
    ! [C_109] :
      ( k1_xboole_0 = C_109
      | ~ r1_tarski(C_109,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1107,c_4])).

tff(c_1637,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,k2_xboole_0(B_12,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1625])).

tff(c_1655,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_1637])).

tff(c_4270,plain,(
    ! [A_157,B_158] : k4_xboole_0(k3_xboole_0(A_157,B_158),A_157) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4227,c_1655])).

tff(c_5748,plain,(
    ! [A_183,B_184] : k4_xboole_0(k2_xboole_0(A_183,B_184),k4_xboole_0(B_184,A_183)) = k4_xboole_0(A_183,k4_xboole_0(B_184,A_183)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_267])).

tff(c_5811,plain,(
    ! [A_157,B_158] : k4_xboole_0(k2_xboole_0(A_157,k3_xboole_0(A_157,B_158)),k1_xboole_0) = k4_xboole_0(A_157,k4_xboole_0(k3_xboole_0(A_157,B_158),A_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4270,c_5748])).

tff(c_5928,plain,(
    ! [A_157,B_158] : k4_xboole_0(A_157,k4_xboole_0(B_158,A_157)) = A_157 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4801,c_1329,c_18,c_22,c_5811])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_10),B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    ! [A_30,B_31,C_32] :
      ( k4_xboole_0(k2_tarski(A_30,B_31),C_32) = k2_tarski(A_30,B_31)
      | r2_hidden(B_31,C_32)
      | r2_hidden(A_30,C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5871,plain,(
    ! [C_32,A_30,B_31] :
      ( k4_xboole_0(k2_xboole_0(C_32,k2_tarski(A_30,B_31)),k2_tarski(A_30,B_31)) = k4_xboole_0(C_32,k4_xboole_0(k2_tarski(A_30,B_31),C_32))
      | r2_hidden(B_31,C_32)
      | r2_hidden(A_30,C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5748])).

tff(c_5947,plain,(
    ! [C_32,A_30,B_31] :
      ( k4_xboole_0(C_32,k4_xboole_0(k2_tarski(A_30,B_31),C_32)) = k4_xboole_0(C_32,k2_tarski(A_30,B_31))
      | r2_hidden(B_31,C_32)
      | r2_hidden(A_30,C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5871])).

tff(c_177576,plain,(
    ! [C_1284,A_1285,B_1286] :
      ( k4_xboole_0(C_1284,k2_tarski(A_1285,B_1286)) = C_1284
      | r2_hidden(B_1286,C_1284)
      | r2_hidden(A_1285,C_1284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5928,c_5947])).

tff(c_44,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_178236,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_177576,c_44])).

tff(c_178437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46,c_178236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 44.18/35.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.18/35.30  
% 44.18/35.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.18/35.30  %$ r2_hidden > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 44.18/35.30  
% 44.18/35.30  %Foreground sorts:
% 44.18/35.30  
% 44.18/35.30  
% 44.18/35.30  %Background operators:
% 44.18/35.30  
% 44.18/35.30  
% 44.18/35.30  %Foreground operators:
% 44.18/35.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 44.18/35.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 44.18/35.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 44.18/35.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 44.18/35.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 44.18/35.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 44.18/35.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 44.18/35.30  tff('#skF_2', type, '#skF_2': $i).
% 44.18/35.30  tff('#skF_3', type, '#skF_3': $i).
% 44.18/35.30  tff('#skF_1', type, '#skF_1': $i).
% 44.18/35.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 44.18/35.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 44.18/35.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 44.18/35.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 44.18/35.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 44.18/35.30  
% 44.18/35.31  tff(f_84, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 44.18/35.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 44.18/35.31  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 44.18/35.31  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 44.18/35.31  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 44.18/35.31  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 44.18/35.31  tff(f_61, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 44.18/35.31  tff(f_65, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 44.18/35.31  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 44.18/35.31  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 44.18/35.31  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 44.18/35.31  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 44.18/35.31  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 44.18/35.31  tff(f_73, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 44.18/35.31  tff(c_48, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 44.18/35.31  tff(c_46, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 44.18/35.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 44.18/35.31  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 44.18/35.31  tff(c_74, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 44.18/35.31  tff(c_24, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 44.18/35.31  tff(c_89, plain, (![A_39, B_38]: (r1_tarski(A_39, k2_xboole_0(B_38, A_39)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_24])).
% 44.18/35.31  tff(c_557, plain, (![A_72, B_73, C_74]: (r1_tarski(k4_xboole_0(A_72, B_73), C_74) | ~r1_tarski(A_72, k2_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 44.18/35.31  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 44.18/35.31  tff(c_3955, plain, (![A_152, B_153, C_154]: (k2_xboole_0(k4_xboole_0(A_152, B_153), C_154)=C_154 | ~r1_tarski(A_152, k2_xboole_0(B_153, C_154)))), inference(resolution, [status(thm)], [c_557, c_10])).
% 44.18/35.31  tff(c_4041, plain, (![A_155, B_156]: (k2_xboole_0(k4_xboole_0(A_155, B_156), A_155)=A_155)), inference(resolution, [status(thm)], [c_89, c_3955])).
% 44.18/35.31  tff(c_4674, plain, (![A_166, B_167]: (k2_xboole_0(k3_xboole_0(A_166, B_167), A_166)=A_166)), inference(superposition, [status(thm), theory('equality')], [c_20, c_4041])).
% 44.18/35.31  tff(c_4801, plain, (![A_1, B_167]: (k2_xboole_0(A_1, k3_xboole_0(A_1, B_167))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4674])).
% 44.18/35.31  tff(c_32, plain, (![B_26]: (k2_zfmisc_1(k1_xboole_0, B_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 44.18/35.31  tff(c_1003, plain, (![C_95, A_96, B_97]: (k4_xboole_0(k2_zfmisc_1(C_95, A_96), k2_zfmisc_1(C_95, B_97))=k2_zfmisc_1(C_95, k4_xboole_0(A_96, B_97)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 44.18/35.31  tff(c_1052, plain, (![B_97, B_26]: (k4_xboole_0(k1_xboole_0, k2_zfmisc_1(k1_xboole_0, B_97))=k2_zfmisc_1(k1_xboole_0, k4_xboole_0(B_26, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1003])).
% 44.18/35.31  tff(c_1060, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_1052])).
% 44.18/35.31  tff(c_16, plain, (![A_11, B_12, C_13]: (r1_tarski(k4_xboole_0(A_11, B_12), C_13) | ~r1_tarski(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 44.18/35.31  tff(c_1071, plain, (![C_13]: (r1_tarski(k1_xboole_0, C_13) | ~r1_tarski(k1_xboole_0, k2_xboole_0(k1_xboole_0, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_1060, c_16])).
% 44.18/35.31  tff(c_1107, plain, (![C_98]: (r1_tarski(k1_xboole_0, C_98))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1071])).
% 44.18/35.31  tff(c_1114, plain, (![C_98]: (k2_xboole_0(k1_xboole_0, C_98)=C_98)), inference(resolution, [status(thm)], [c_1107, c_10])).
% 44.18/35.31  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 44.18/35.31  tff(c_1212, plain, (![C_102]: (k2_xboole_0(k1_xboole_0, C_102)=C_102)), inference(resolution, [status(thm)], [c_1107, c_10])).
% 44.18/35.31  tff(c_1298, plain, (![B_8]: (k4_xboole_0(B_8, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1212])).
% 44.18/35.31  tff(c_1329, plain, (![B_8]: (k4_xboole_0(B_8, k1_xboole_0)=B_8)), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_1298])).
% 44.18/35.31  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 44.18/35.31  tff(c_22, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k3_xboole_0(A_18, B_19), C_20)=k3_xboole_0(A_18, k4_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 44.18/35.31  tff(c_207, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k4_xboole_0(B_54, A_53))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 44.18/35.31  tff(c_213, plain, (![B_54, A_53]: (r1_tarski(k4_xboole_0(B_54, A_53), k2_xboole_0(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_207, c_89])).
% 44.18/35.31  tff(c_4115, plain, (![A_155, B_156]: (r1_tarski(k4_xboole_0(A_155, k4_xboole_0(A_155, B_156)), A_155))), inference(superposition, [status(thm), theory('equality')], [c_4041, c_213])).
% 44.18/35.31  tff(c_4227, plain, (![A_157, B_158]: (r1_tarski(k3_xboole_0(A_157, B_158), A_157))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4115])).
% 44.18/35.31  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 44.18/35.31  tff(c_122, plain, (![A_42, B_43]: (k2_xboole_0(A_42, B_43)=B_43 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 44.18/35.31  tff(c_134, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_122])).
% 44.18/35.31  tff(c_267, plain, (![A_58, B_59]: (k4_xboole_0(k2_xboole_0(A_58, B_59), B_59)=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 44.18/35.31  tff(c_276, plain, (![B_59, A_58]: (k2_xboole_0(B_59, k4_xboole_0(A_58, B_59))=k2_xboole_0(B_59, k2_xboole_0(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_267, c_12])).
% 44.18/35.31  tff(c_296, plain, (![B_59, A_58]: (k2_xboole_0(B_59, k2_xboole_0(A_58, B_59))=k2_xboole_0(B_59, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_276])).
% 44.18/35.31  tff(c_1224, plain, (![C_102]: (k2_xboole_0(C_102, k1_xboole_0)=k2_xboole_0(C_102, C_102))), inference(superposition, [status(thm), theory('equality')], [c_1212, c_296])).
% 44.18/35.31  tff(c_1313, plain, (![C_102]: (k2_xboole_0(C_102, k1_xboole_0)=C_102)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_1224])).
% 44.18/35.31  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 44.18/35.31  tff(c_1625, plain, (![C_109]: (k1_xboole_0=C_109 | ~r1_tarski(C_109, k1_xboole_0))), inference(resolution, [status(thm)], [c_1107, c_4])).
% 44.18/35.31  tff(c_1637, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, k2_xboole_0(B_12, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_1625])).
% 44.18/35.31  tff(c_1655, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_1637])).
% 44.18/35.31  tff(c_4270, plain, (![A_157, B_158]: (k4_xboole_0(k3_xboole_0(A_157, B_158), A_157)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4227, c_1655])).
% 44.18/35.31  tff(c_5748, plain, (![A_183, B_184]: (k4_xboole_0(k2_xboole_0(A_183, B_184), k4_xboole_0(B_184, A_183))=k4_xboole_0(A_183, k4_xboole_0(B_184, A_183)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_267])).
% 44.18/35.31  tff(c_5811, plain, (![A_157, B_158]: (k4_xboole_0(k2_xboole_0(A_157, k3_xboole_0(A_157, B_158)), k1_xboole_0)=k4_xboole_0(A_157, k4_xboole_0(k3_xboole_0(A_157, B_158), A_157)))), inference(superposition, [status(thm), theory('equality')], [c_4270, c_5748])).
% 44.18/35.31  tff(c_5928, plain, (![A_157, B_158]: (k4_xboole_0(A_157, k4_xboole_0(B_158, A_157))=A_157)), inference(demodulation, [status(thm), theory('equality')], [c_4801, c_1329, c_18, c_22, c_5811])).
% 44.18/35.31  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_10), B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 44.18/35.31  tff(c_38, plain, (![A_30, B_31, C_32]: (k4_xboole_0(k2_tarski(A_30, B_31), C_32)=k2_tarski(A_30, B_31) | r2_hidden(B_31, C_32) | r2_hidden(A_30, C_32))), inference(cnfTransformation, [status(thm)], [f_73])).
% 44.18/35.31  tff(c_5871, plain, (![C_32, A_30, B_31]: (k4_xboole_0(k2_xboole_0(C_32, k2_tarski(A_30, B_31)), k2_tarski(A_30, B_31))=k4_xboole_0(C_32, k4_xboole_0(k2_tarski(A_30, B_31), C_32)) | r2_hidden(B_31, C_32) | r2_hidden(A_30, C_32))), inference(superposition, [status(thm), theory('equality')], [c_38, c_5748])).
% 44.18/35.31  tff(c_5947, plain, (![C_32, A_30, B_31]: (k4_xboole_0(C_32, k4_xboole_0(k2_tarski(A_30, B_31), C_32))=k4_xboole_0(C_32, k2_tarski(A_30, B_31)) | r2_hidden(B_31, C_32) | r2_hidden(A_30, C_32))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5871])).
% 44.18/35.31  tff(c_177576, plain, (![C_1284, A_1285, B_1286]: (k4_xboole_0(C_1284, k2_tarski(A_1285, B_1286))=C_1284 | r2_hidden(B_1286, C_1284) | r2_hidden(A_1285, C_1284))), inference(demodulation, [status(thm), theory('equality')], [c_5928, c_5947])).
% 44.18/35.31  tff(c_44, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_84])).
% 44.18/35.31  tff(c_178236, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_177576, c_44])).
% 44.18/35.31  tff(c_178437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_46, c_178236])).
% 44.18/35.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.18/35.31  
% 44.18/35.31  Inference rules
% 44.18/35.31  ----------------------
% 44.18/35.31  #Ref     : 0
% 44.18/35.31  #Sup     : 44369
% 44.18/35.31  #Fact    : 6
% 44.18/35.31  #Define  : 0
% 44.18/35.31  #Split   : 0
% 44.18/35.31  #Chain   : 0
% 44.18/35.31  #Close   : 0
% 44.18/35.31  
% 44.18/35.31  Ordering : KBO
% 44.18/35.31  
% 44.18/35.31  Simplification rules
% 44.18/35.31  ----------------------
% 44.18/35.31  #Subsume      : 2159
% 44.18/35.31  #Demod        : 57330
% 44.18/35.31  #Tautology    : 27278
% 44.18/35.31  #SimpNegUnit  : 59
% 44.18/35.31  #BackRed      : 19
% 44.18/35.31  
% 44.18/35.31  #Partial instantiations: 0
% 44.18/35.31  #Strategies tried      : 1
% 44.18/35.31  
% 44.18/35.31  Timing (in seconds)
% 44.18/35.32  ----------------------
% 44.38/35.32  Preprocessing        : 0.30
% 44.38/35.32  Parsing              : 0.15
% 44.38/35.32  CNF conversion       : 0.02
% 44.38/35.32  Main loop            : 34.12
% 44.38/35.32  Inferencing          : 2.85
% 44.38/35.32  Reduction            : 22.24
% 44.38/35.32  Demodulation         : 20.63
% 44.38/35.32  BG Simplification    : 0.40
% 44.38/35.32  Subsumption          : 7.17
% 44.38/35.32  Abstraction          : 0.74
% 44.38/35.32  MUC search           : 0.00
% 44.38/35.32  Cooper               : 0.00
% 44.38/35.32  Total                : 34.46
% 44.38/35.32  Index Insertion      : 0.00
% 44.38/35.32  Index Deletion       : 0.00
% 44.38/35.32  Index Matching       : 0.00
% 44.38/35.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
