%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:52 EST 2020

% Result     : Theorem 13.05s
% Output     : CNFRefutation 13.05s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 450 expanded)
%              Number of leaves         :   22 ( 161 expanded)
%              Depth                    :   18
%              Number of atoms          :   85 ( 543 expanded)
%              Number of equality atoms :   70 ( 377 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_224,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_416,plain,(
    ! [A_52] : k4_xboole_0(A_52,A_52) = k3_xboole_0(A_52,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_224])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_422,plain,(
    ! [A_52,C_8] : k4_xboole_0(k3_xboole_0(A_52,k1_xboole_0),C_8) = k4_xboole_0(A_52,k2_xboole_0(A_52,C_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_8])).

tff(c_599,plain,(
    ! [A_58,C_59] : k4_xboole_0(k3_xboole_0(A_58,k1_xboole_0),C_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_422])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    ! [B_27,A_28] :
      ( r1_xboole_0(B_27,A_28)
      | ~ r1_xboole_0(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [B_15,A_14] : r1_xboole_0(B_15,k4_xboole_0(A_14,B_15)) ),
    inference(resolution,[status(thm)],[c_16,c_58])).

tff(c_88,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = A_34
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_105,plain,(
    ! [B_15,A_14] : k4_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = B_15 ),
    inference(resolution,[status(thm)],[c_64,c_88])).

tff(c_629,plain,(
    ! [A_58] : k3_xboole_0(A_58,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_105])).

tff(c_695,plain,(
    ! [A_60] : k3_xboole_0(A_60,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_105])).

tff(c_22,plain,(
    ! [A_18,B_19] : k5_xboole_0(k5_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_700,plain,(
    ! [A_60] : k5_xboole_0(k5_xboole_0(A_60,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_695,c_22])).

tff(c_718,plain,(
    ! [A_60] : k2_xboole_0(A_60,k1_xboole_0) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_700])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_276,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_224])).

tff(c_772,plain,(
    ! [A_63] : k4_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_276])).

tff(c_784,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(B_7,k4_xboole_0(A_6,B_7))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_8])).

tff(c_823,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(B_7,A_6)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_784])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_188,plain,(
    ! [B_39,A_40] :
      ( r1_xboole_0(B_39,A_40)
      | k4_xboole_0(A_40,B_39) != A_40 ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2197,plain,(
    ! [B_108,A_109] :
      ( k4_xboole_0(B_108,A_109) = B_108
      | k4_xboole_0(A_109,B_108) != A_109 ) ),
    inference(resolution,[status(thm)],[c_188,c_18])).

tff(c_2211,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k4_xboole_0(A_11,B_12)
      | k3_xboole_0(A_11,B_12) != A_11 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2197])).

tff(c_3832,plain,(
    ! [A_139,B_140] :
      ( k4_xboole_0(A_139,B_140) = k1_xboole_0
      | k3_xboole_0(A_139,B_140) != A_139 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_8,c_2211])).

tff(c_3961,plain,(
    ! [B_140,A_139] :
      ( k2_xboole_0(B_140,k1_xboole_0) = k2_xboole_0(B_140,A_139)
      | k3_xboole_0(A_139,B_140) != A_139 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3832,c_4])).

tff(c_4854,plain,(
    ! [B_156,A_157] :
      ( k2_xboole_0(B_156,A_157) = B_156
      | k3_xboole_0(A_157,B_156) != A_157 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_3961])).

tff(c_4925,plain,(
    ! [A_158] :
      ( k2_xboole_0(k1_xboole_0,A_158) = k1_xboole_0
      | k1_xboole_0 != A_158 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_4854])).

tff(c_690,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_276])).

tff(c_1231,plain,(
    ! [A_82,B_83] : k4_xboole_0(k4_xboole_0(A_82,B_83),B_83) = k4_xboole_0(A_82,B_83) ),
    inference(resolution,[status(thm)],[c_16,c_88])).

tff(c_1266,plain,(
    ! [A_82,B_83] : k4_xboole_0(k4_xboole_0(A_82,B_83),k4_xboole_0(A_82,B_83)) = k3_xboole_0(k4_xboole_0(A_82,B_83),B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_12])).

tff(c_1347,plain,(
    ! [A_84,B_85] : k3_xboole_0(k4_xboole_0(A_84,B_85),B_85) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_1266])).

tff(c_1378,plain,(
    ! [A_6,B_7,C_8] : k3_xboole_0(k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)),C_8) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1347])).

tff(c_4952,plain,(
    ! [A_6,A_158] :
      ( k3_xboole_0(k4_xboole_0(A_6,k1_xboole_0),A_158) = k1_xboole_0
      | k1_xboole_0 != A_158 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4925,c_1378])).

tff(c_7161,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4952])).

tff(c_291,plain,(
    ! [A_46,B_47,C_48] : k4_xboole_0(k4_xboole_0(A_46,B_47),C_48) = k4_xboole_0(A_46,k2_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_310,plain,(
    ! [C_48,A_46,B_47] : k4_xboole_0(C_48,k4_xboole_0(A_46,k2_xboole_0(B_47,C_48))) = C_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_105])).

tff(c_4958,plain,(
    ! [A_158,A_46] :
      ( k4_xboole_0(A_158,k4_xboole_0(A_46,k1_xboole_0)) = A_158
      | k1_xboole_0 != A_158 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4925,c_310])).

tff(c_7349,plain,(
    ! [A_185,A_186] :
      ( k4_xboole_0(A_185,A_186) = A_185
      | k1_xboole_0 != A_185 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4958])).

tff(c_7863,plain,(
    ! [A_189,B_190] :
      ( k3_xboole_0(A_189,B_190) = A_189
      | k1_xboole_0 != A_189 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_7349])).

tff(c_4082,plain,(
    ! [B_140,A_139] :
      ( k2_xboole_0(B_140,A_139) = B_140
      | k3_xboole_0(A_139,B_140) != A_139 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_3961])).

tff(c_8080,plain,(
    ! [B_190] : k2_xboole_0(B_190,k1_xboole_0) = B_190 ),
    inference(superposition,[status(thm),theory(equality)],[c_7863,c_4082])).

tff(c_1384,plain,(
    ! [B_15,A_14] : k3_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_1347])).

tff(c_475,plain,(
    ! [A_53,B_54] : k5_xboole_0(k5_xboole_0(A_53,B_54),k3_xboole_0(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_11655,plain,(
    ! [A_249,B_250] : k5_xboole_0(k2_xboole_0(A_249,B_250),k3_xboole_0(k5_xboole_0(A_249,B_250),k3_xboole_0(A_249,B_250))) = k2_xboole_0(k5_xboole_0(A_249,B_250),k3_xboole_0(A_249,B_250)) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_22])).

tff(c_11754,plain,(
    ! [B_15,A_14] : k5_xboole_0(k2_xboole_0(B_15,k4_xboole_0(A_14,B_15)),k3_xboole_0(k5_xboole_0(B_15,k4_xboole_0(A_14,B_15)),k1_xboole_0)) = k2_xboole_0(k5_xboole_0(B_15,k4_xboole_0(A_14,B_15)),k3_xboole_0(B_15,k4_xboole_0(A_14,B_15))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1384,c_11655])).

tff(c_11804,plain,(
    ! [B_15,A_14] : k5_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = k2_xboole_0(B_15,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_7161,c_8080,c_1384,c_4,c_11754])).

tff(c_24,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52049,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11804,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:19:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.05/6.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.05/6.27  
% 13.05/6.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.05/6.27  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 13.05/6.27  
% 13.05/6.27  %Foreground sorts:
% 13.05/6.27  
% 13.05/6.27  
% 13.05/6.27  %Background operators:
% 13.05/6.27  
% 13.05/6.27  
% 13.05/6.27  %Foreground operators:
% 13.05/6.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.05/6.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.05/6.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.05/6.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.05/6.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.05/6.27  tff('#skF_2', type, '#skF_2': $i).
% 13.05/6.27  tff('#skF_1', type, '#skF_1': $i).
% 13.05/6.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.05/6.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.05/6.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.05/6.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.05/6.27  
% 13.05/6.29  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 13.05/6.29  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.05/6.29  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 13.05/6.29  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.05/6.29  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 13.05/6.29  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 13.05/6.29  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 13.05/6.29  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 13.05/6.29  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 13.05/6.29  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.05/6.29  tff(f_52, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 13.05/6.29  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.05/6.29  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.05/6.29  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.05/6.29  tff(c_224, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.05/6.29  tff(c_416, plain, (![A_52]: (k4_xboole_0(A_52, A_52)=k3_xboole_0(A_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_224])).
% 13.05/6.29  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.05/6.29  tff(c_422, plain, (![A_52, C_8]: (k4_xboole_0(k3_xboole_0(A_52, k1_xboole_0), C_8)=k4_xboole_0(A_52, k2_xboole_0(A_52, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_416, c_8])).
% 13.05/6.29  tff(c_599, plain, (![A_58, C_59]: (k4_xboole_0(k3_xboole_0(A_58, k1_xboole_0), C_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_422])).
% 13.05/6.29  tff(c_16, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.05/6.29  tff(c_58, plain, (![B_27, A_28]: (r1_xboole_0(B_27, A_28) | ~r1_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.05/6.29  tff(c_64, plain, (![B_15, A_14]: (r1_xboole_0(B_15, k4_xboole_0(A_14, B_15)))), inference(resolution, [status(thm)], [c_16, c_58])).
% 13.05/6.29  tff(c_88, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=A_34 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.05/6.29  tff(c_105, plain, (![B_15, A_14]: (k4_xboole_0(B_15, k4_xboole_0(A_14, B_15))=B_15)), inference(resolution, [status(thm)], [c_64, c_88])).
% 13.05/6.29  tff(c_629, plain, (![A_58]: (k3_xboole_0(A_58, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_599, c_105])).
% 13.05/6.29  tff(c_695, plain, (![A_60]: (k3_xboole_0(A_60, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_599, c_105])).
% 13.05/6.29  tff(c_22, plain, (![A_18, B_19]: (k5_xboole_0(k5_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.05/6.29  tff(c_700, plain, (![A_60]: (k5_xboole_0(k5_xboole_0(A_60, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_695, c_22])).
% 13.05/6.29  tff(c_718, plain, (![A_60]: (k2_xboole_0(A_60, k1_xboole_0)=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_700])).
% 13.05/6.29  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.05/6.29  tff(c_276, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_224])).
% 13.05/6.29  tff(c_772, plain, (![A_63]: (k4_xboole_0(A_63, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_629, c_276])).
% 13.05/6.29  tff(c_784, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(B_7, k4_xboole_0(A_6, B_7)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_772, c_8])).
% 13.05/6.29  tff(c_823, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(B_7, A_6))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_784])).
% 13.05/6.29  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.05/6.29  tff(c_84, plain, (![A_32, B_33]: (r1_xboole_0(A_32, B_33) | k4_xboole_0(A_32, B_33)!=A_32)), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.05/6.29  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.05/6.29  tff(c_188, plain, (![B_39, A_40]: (r1_xboole_0(B_39, A_40) | k4_xboole_0(A_40, B_39)!=A_40)), inference(resolution, [status(thm)], [c_84, c_2])).
% 13.05/6.29  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.05/6.29  tff(c_2197, plain, (![B_108, A_109]: (k4_xboole_0(B_108, A_109)=B_108 | k4_xboole_0(A_109, B_108)!=A_109)), inference(resolution, [status(thm)], [c_188, c_18])).
% 13.05/6.29  tff(c_2211, plain, (![A_11, B_12]: (k4_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k4_xboole_0(A_11, B_12) | k3_xboole_0(A_11, B_12)!=A_11)), inference(superposition, [status(thm), theory('equality')], [c_12, c_2197])).
% 13.05/6.29  tff(c_3832, plain, (![A_139, B_140]: (k4_xboole_0(A_139, B_140)=k1_xboole_0 | k3_xboole_0(A_139, B_140)!=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_823, c_8, c_2211])).
% 13.05/6.29  tff(c_3961, plain, (![B_140, A_139]: (k2_xboole_0(B_140, k1_xboole_0)=k2_xboole_0(B_140, A_139) | k3_xboole_0(A_139, B_140)!=A_139)), inference(superposition, [status(thm), theory('equality')], [c_3832, c_4])).
% 13.05/6.29  tff(c_4854, plain, (![B_156, A_157]: (k2_xboole_0(B_156, A_157)=B_156 | k3_xboole_0(A_157, B_156)!=A_157)), inference(demodulation, [status(thm), theory('equality')], [c_718, c_3961])).
% 13.05/6.29  tff(c_4925, plain, (![A_158]: (k2_xboole_0(k1_xboole_0, A_158)=k1_xboole_0 | k1_xboole_0!=A_158)), inference(superposition, [status(thm), theory('equality')], [c_629, c_4854])).
% 13.05/6.29  tff(c_690, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_629, c_276])).
% 13.05/6.29  tff(c_1231, plain, (![A_82, B_83]: (k4_xboole_0(k4_xboole_0(A_82, B_83), B_83)=k4_xboole_0(A_82, B_83))), inference(resolution, [status(thm)], [c_16, c_88])).
% 13.05/6.29  tff(c_1266, plain, (![A_82, B_83]: (k4_xboole_0(k4_xboole_0(A_82, B_83), k4_xboole_0(A_82, B_83))=k3_xboole_0(k4_xboole_0(A_82, B_83), B_83))), inference(superposition, [status(thm), theory('equality')], [c_1231, c_12])).
% 13.05/6.29  tff(c_1347, plain, (![A_84, B_85]: (k3_xboole_0(k4_xboole_0(A_84, B_85), B_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_690, c_1266])).
% 13.05/6.29  tff(c_1378, plain, (![A_6, B_7, C_8]: (k3_xboole_0(k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)), C_8)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_1347])).
% 13.05/6.29  tff(c_4952, plain, (![A_6, A_158]: (k3_xboole_0(k4_xboole_0(A_6, k1_xboole_0), A_158)=k1_xboole_0 | k1_xboole_0!=A_158)), inference(superposition, [status(thm), theory('equality')], [c_4925, c_1378])).
% 13.05/6.29  tff(c_7161, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4952])).
% 13.05/6.29  tff(c_291, plain, (![A_46, B_47, C_48]: (k4_xboole_0(k4_xboole_0(A_46, B_47), C_48)=k4_xboole_0(A_46, k2_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.05/6.29  tff(c_310, plain, (![C_48, A_46, B_47]: (k4_xboole_0(C_48, k4_xboole_0(A_46, k2_xboole_0(B_47, C_48)))=C_48)), inference(superposition, [status(thm), theory('equality')], [c_291, c_105])).
% 13.05/6.29  tff(c_4958, plain, (![A_158, A_46]: (k4_xboole_0(A_158, k4_xboole_0(A_46, k1_xboole_0))=A_158 | k1_xboole_0!=A_158)), inference(superposition, [status(thm), theory('equality')], [c_4925, c_310])).
% 13.05/6.29  tff(c_7349, plain, (![A_185, A_186]: (k4_xboole_0(A_185, A_186)=A_185 | k1_xboole_0!=A_185)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4958])).
% 13.05/6.29  tff(c_7863, plain, (![A_189, B_190]: (k3_xboole_0(A_189, B_190)=A_189 | k1_xboole_0!=A_189)), inference(superposition, [status(thm), theory('equality')], [c_12, c_7349])).
% 13.05/6.29  tff(c_4082, plain, (![B_140, A_139]: (k2_xboole_0(B_140, A_139)=B_140 | k3_xboole_0(A_139, B_140)!=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_718, c_3961])).
% 13.05/6.29  tff(c_8080, plain, (![B_190]: (k2_xboole_0(B_190, k1_xboole_0)=B_190)), inference(superposition, [status(thm), theory('equality')], [c_7863, c_4082])).
% 13.05/6.29  tff(c_1384, plain, (![B_15, A_14]: (k3_xboole_0(B_15, k4_xboole_0(A_14, B_15))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_105, c_1347])).
% 13.05/6.29  tff(c_475, plain, (![A_53, B_54]: (k5_xboole_0(k5_xboole_0(A_53, B_54), k3_xboole_0(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.05/6.29  tff(c_11655, plain, (![A_249, B_250]: (k5_xboole_0(k2_xboole_0(A_249, B_250), k3_xboole_0(k5_xboole_0(A_249, B_250), k3_xboole_0(A_249, B_250)))=k2_xboole_0(k5_xboole_0(A_249, B_250), k3_xboole_0(A_249, B_250)))), inference(superposition, [status(thm), theory('equality')], [c_475, c_22])).
% 13.05/6.29  tff(c_11754, plain, (![B_15, A_14]: (k5_xboole_0(k2_xboole_0(B_15, k4_xboole_0(A_14, B_15)), k3_xboole_0(k5_xboole_0(B_15, k4_xboole_0(A_14, B_15)), k1_xboole_0))=k2_xboole_0(k5_xboole_0(B_15, k4_xboole_0(A_14, B_15)), k3_xboole_0(B_15, k4_xboole_0(A_14, B_15))))), inference(superposition, [status(thm), theory('equality')], [c_1384, c_11655])).
% 13.05/6.29  tff(c_11804, plain, (![B_15, A_14]: (k5_xboole_0(B_15, k4_xboole_0(A_14, B_15))=k2_xboole_0(B_15, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_7161, c_8080, c_1384, c_4, c_11754])).
% 13.05/6.29  tff(c_24, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.05/6.29  tff(c_52049, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11804, c_24])).
% 13.05/6.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.05/6.29  
% 13.05/6.29  Inference rules
% 13.05/6.29  ----------------------
% 13.05/6.29  #Ref     : 0
% 13.05/6.29  #Sup     : 13240
% 13.05/6.29  #Fact    : 0
% 13.05/6.29  #Define  : 0
% 13.05/6.29  #Split   : 5
% 13.05/6.29  #Chain   : 0
% 13.05/6.29  #Close   : 0
% 13.05/6.29  
% 13.05/6.29  Ordering : KBO
% 13.05/6.29  
% 13.05/6.29  Simplification rules
% 13.05/6.29  ----------------------
% 13.05/6.29  #Subsume      : 1693
% 13.05/6.29  #Demod        : 11906
% 13.05/6.29  #Tautology    : 8888
% 13.05/6.29  #SimpNegUnit  : 0
% 13.05/6.29  #BackRed      : 9
% 13.05/6.29  
% 13.05/6.29  #Partial instantiations: 0
% 13.05/6.29  #Strategies tried      : 1
% 13.05/6.29  
% 13.05/6.29  Timing (in seconds)
% 13.05/6.29  ----------------------
% 13.05/6.29  Preprocessing        : 0.26
% 13.05/6.29  Parsing              : 0.15
% 13.05/6.29  CNF conversion       : 0.02
% 13.05/6.29  Main loop            : 5.21
% 13.05/6.29  Inferencing          : 0.92
% 13.05/6.29  Reduction            : 3.06
% 13.05/6.29  Demodulation         : 2.71
% 13.05/6.29  BG Simplification    : 0.10
% 13.05/6.29  Subsumption          : 0.92
% 13.05/6.29  Abstraction          : 0.19
% 13.05/6.29  MUC search           : 0.00
% 13.05/6.29  Cooper               : 0.00
% 13.05/6.29  Total                : 5.51
% 13.05/6.29  Index Insertion      : 0.00
% 13.05/6.29  Index Deletion       : 0.00
% 13.05/6.29  Index Matching       : 0.00
% 13.05/6.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
