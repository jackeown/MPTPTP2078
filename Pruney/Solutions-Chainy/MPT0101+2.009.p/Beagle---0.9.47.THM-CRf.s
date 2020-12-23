%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:40 EST 2020

% Result     : Theorem 43.32s
% Output     : CNFRefutation 43.48s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 103 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   42 (  99 expanded)
%              Number of equality atoms :   37 (  86 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_578,plain,(
    ! [A_63,B_64] : k2_xboole_0(k5_xboole_0(A_63,B_64),k3_xboole_0(A_63,B_64)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_590,plain,(
    ! [A_63,B_64] : k2_xboole_0(k3_xboole_0(A_63,B_64),k5_xboole_0(A_63,B_64)) = k2_xboole_0(A_63,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_2])).

tff(c_364,plain,(
    ! [A_53,B_54] : k2_xboole_0(k4_xboole_0(A_53,B_54),k4_xboole_0(B_54,A_53)) = k5_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_880,plain,(
    ! [B_81,A_82] : k2_xboole_0(k4_xboole_0(B_81,A_82),k4_xboole_0(A_82,B_81)) = k5_xboole_0(A_82,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),k4_xboole_0(B_6,A_5)) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_911,plain,(
    ! [B_81,A_82] : k5_xboole_0(B_81,A_82) = k5_xboole_0(A_82,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_6])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = A_26
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [A_38,B_39] : k4_xboole_0(k4_xboole_0(A_38,B_39),B_39) = k4_xboole_0(A_38,B_39) ),
    inference(resolution,[status(thm)],[c_14,c_90])).

tff(c_193,plain,(
    ! [A_12,B_13] : k4_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_163])).

tff(c_3110,plain,(
    ! [A_174,B_175] : k4_xboole_0(k3_xboole_0(A_174,B_175),k4_xboole_0(A_174,B_175)) = k3_xboole_0(A_174,B_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_193])).

tff(c_3237,plain,(
    ! [A_3,B_4] : k4_xboole_0(k3_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k3_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3110])).

tff(c_376,plain,(
    ! [B_54,A_53] : k2_xboole_0(k4_xboole_0(B_54,A_53),k4_xboole_0(A_53,B_54)) = k5_xboole_0(A_53,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_2])).

tff(c_243,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k4_xboole_0(A_44,B_45),C_46) = k4_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4814,plain,(
    ! [A_195,B_196,C_197] : k4_xboole_0(A_195,k2_xboole_0(k4_xboole_0(A_195,B_196),C_197)) = k4_xboole_0(k3_xboole_0(A_195,B_196),C_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_243])).

tff(c_5033,plain,(
    ! [B_54,A_53] : k4_xboole_0(k3_xboole_0(B_54,A_53),k4_xboole_0(A_53,B_54)) = k4_xboole_0(B_54,k5_xboole_0(A_53,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_4814])).

tff(c_5106,plain,(
    ! [B_54,A_53] : k4_xboole_0(B_54,k5_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3237,c_5033])).

tff(c_5113,plain,(
    ! [B_198,A_199] : k4_xboole_0(B_198,k5_xboole_0(A_199,B_198)) = k3_xboole_0(A_199,B_198) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3237,c_5033])).

tff(c_94,plain,(
    ! [A_14,B_15] : k4_xboole_0(k4_xboole_0(A_14,B_15),B_15) = k4_xboole_0(A_14,B_15) ),
    inference(resolution,[status(thm)],[c_14,c_90])).

tff(c_5219,plain,(
    ! [A_199,B_198] : k4_xboole_0(k3_xboole_0(A_199,B_198),k5_xboole_0(A_199,B_198)) = k4_xboole_0(B_198,k5_xboole_0(A_199,B_198)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5113,c_94])).

tff(c_107347,plain,(
    ! [A_962,B_963] : k4_xboole_0(k3_xboole_0(A_962,B_963),k5_xboole_0(A_962,B_963)) = k3_xboole_0(A_962,B_963) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5106,c_5219])).

tff(c_107737,plain,(
    ! [A_962,B_963] : k2_xboole_0(k3_xboole_0(A_962,B_963),k4_xboole_0(k5_xboole_0(A_962,B_963),k3_xboole_0(A_962,B_963))) = k5_xboole_0(k5_xboole_0(A_962,B_963),k3_xboole_0(A_962,B_963)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107347,c_376])).

tff(c_108059,plain,(
    ! [A_962,B_963] : k5_xboole_0(k3_xboole_0(A_962,B_963),k5_xboole_0(A_962,B_963)) = k2_xboole_0(A_962,B_963) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_911,c_8,c_107737])).

tff(c_22,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_971,plain,(
    k5_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_22])).

tff(c_117923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108059,c_971])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:27:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.32/33.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.41/33.39  
% 43.41/33.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.41/33.39  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 43.41/33.39  
% 43.41/33.39  %Foreground sorts:
% 43.41/33.39  
% 43.41/33.39  
% 43.41/33.39  %Background operators:
% 43.41/33.39  
% 43.41/33.39  
% 43.41/33.39  %Foreground operators:
% 43.41/33.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.41/33.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 43.41/33.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 43.41/33.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 43.41/33.39  tff('#skF_2', type, '#skF_2': $i).
% 43.41/33.39  tff('#skF_1', type, '#skF_1': $i).
% 43.41/33.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.41/33.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.41/33.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 43.41/33.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 43.41/33.39  
% 43.48/33.41  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 43.48/33.41  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 43.48/33.41  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 43.48/33.41  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 43.48/33.41  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 43.48/33.41  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 43.48/33.41  tff(f_39, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 43.48/33.41  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 43.48/33.41  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 43.48/33.41  tff(f_48, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 43.48/33.41  tff(c_578, plain, (![A_63, B_64]: (k2_xboole_0(k5_xboole_0(A_63, B_64), k3_xboole_0(A_63, B_64))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_45])).
% 43.48/33.41  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 43.48/33.41  tff(c_590, plain, (![A_63, B_64]: (k2_xboole_0(k3_xboole_0(A_63, B_64), k5_xboole_0(A_63, B_64))=k2_xboole_0(A_63, B_64))), inference(superposition, [status(thm), theory('equality')], [c_578, c_2])).
% 43.48/33.41  tff(c_364, plain, (![A_53, B_54]: (k2_xboole_0(k4_xboole_0(A_53, B_54), k4_xboole_0(B_54, A_53))=k5_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.48/33.41  tff(c_880, plain, (![B_81, A_82]: (k2_xboole_0(k4_xboole_0(B_81, A_82), k4_xboole_0(A_82, B_81))=k5_xboole_0(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_364, c_2])).
% 43.48/33.41  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), k4_xboole_0(B_6, A_5))=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.48/33.41  tff(c_911, plain, (![B_81, A_82]: (k5_xboole_0(B_81, A_82)=k5_xboole_0(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_880, c_6])).
% 43.48/33.41  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 43.48/33.41  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 43.48/33.41  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 43.48/33.41  tff(c_14, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 43.48/33.41  tff(c_90, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=A_26 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 43.48/33.41  tff(c_163, plain, (![A_38, B_39]: (k4_xboole_0(k4_xboole_0(A_38, B_39), B_39)=k4_xboole_0(A_38, B_39))), inference(resolution, [status(thm)], [c_14, c_90])).
% 43.48/33.41  tff(c_193, plain, (![A_12, B_13]: (k4_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=k4_xboole_0(A_12, k4_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_163])).
% 43.48/33.41  tff(c_3110, plain, (![A_174, B_175]: (k4_xboole_0(k3_xboole_0(A_174, B_175), k4_xboole_0(A_174, B_175))=k3_xboole_0(A_174, B_175))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_193])).
% 43.48/33.41  tff(c_3237, plain, (![A_3, B_4]: (k4_xboole_0(k3_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k3_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3110])).
% 43.48/33.41  tff(c_376, plain, (![B_54, A_53]: (k2_xboole_0(k4_xboole_0(B_54, A_53), k4_xboole_0(A_53, B_54))=k5_xboole_0(A_53, B_54))), inference(superposition, [status(thm), theory('equality')], [c_364, c_2])).
% 43.48/33.41  tff(c_243, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k4_xboole_0(A_44, B_45), C_46)=k4_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 43.48/33.41  tff(c_4814, plain, (![A_195, B_196, C_197]: (k4_xboole_0(A_195, k2_xboole_0(k4_xboole_0(A_195, B_196), C_197))=k4_xboole_0(k3_xboole_0(A_195, B_196), C_197))), inference(superposition, [status(thm), theory('equality')], [c_12, c_243])).
% 43.48/33.41  tff(c_5033, plain, (![B_54, A_53]: (k4_xboole_0(k3_xboole_0(B_54, A_53), k4_xboole_0(A_53, B_54))=k4_xboole_0(B_54, k5_xboole_0(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_376, c_4814])).
% 43.48/33.41  tff(c_5106, plain, (![B_54, A_53]: (k4_xboole_0(B_54, k5_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(demodulation, [status(thm), theory('equality')], [c_3237, c_5033])).
% 43.48/33.41  tff(c_5113, plain, (![B_198, A_199]: (k4_xboole_0(B_198, k5_xboole_0(A_199, B_198))=k3_xboole_0(A_199, B_198))), inference(demodulation, [status(thm), theory('equality')], [c_3237, c_5033])).
% 43.48/33.41  tff(c_94, plain, (![A_14, B_15]: (k4_xboole_0(k4_xboole_0(A_14, B_15), B_15)=k4_xboole_0(A_14, B_15))), inference(resolution, [status(thm)], [c_14, c_90])).
% 43.48/33.41  tff(c_5219, plain, (![A_199, B_198]: (k4_xboole_0(k3_xboole_0(A_199, B_198), k5_xboole_0(A_199, B_198))=k4_xboole_0(B_198, k5_xboole_0(A_199, B_198)))), inference(superposition, [status(thm), theory('equality')], [c_5113, c_94])).
% 43.48/33.41  tff(c_107347, plain, (![A_962, B_963]: (k4_xboole_0(k3_xboole_0(A_962, B_963), k5_xboole_0(A_962, B_963))=k3_xboole_0(A_962, B_963))), inference(demodulation, [status(thm), theory('equality')], [c_5106, c_5219])).
% 43.48/33.41  tff(c_107737, plain, (![A_962, B_963]: (k2_xboole_0(k3_xboole_0(A_962, B_963), k4_xboole_0(k5_xboole_0(A_962, B_963), k3_xboole_0(A_962, B_963)))=k5_xboole_0(k5_xboole_0(A_962, B_963), k3_xboole_0(A_962, B_963)))), inference(superposition, [status(thm), theory('equality')], [c_107347, c_376])).
% 43.48/33.41  tff(c_108059, plain, (![A_962, B_963]: (k5_xboole_0(k3_xboole_0(A_962, B_963), k5_xboole_0(A_962, B_963))=k2_xboole_0(A_962, B_963))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_911, c_8, c_107737])).
% 43.48/33.41  tff(c_22, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 43.48/33.41  tff(c_971, plain, (k5_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_911, c_22])).
% 43.48/33.41  tff(c_117923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108059, c_971])).
% 43.48/33.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.48/33.41  
% 43.48/33.41  Inference rules
% 43.48/33.41  ----------------------
% 43.48/33.41  #Ref     : 0
% 43.48/33.41  #Sup     : 30143
% 43.48/33.41  #Fact    : 0
% 43.48/33.41  #Define  : 0
% 43.48/33.41  #Split   : 0
% 43.48/33.41  #Chain   : 0
% 43.48/33.41  #Close   : 0
% 43.48/33.41  
% 43.48/33.41  Ordering : KBO
% 43.48/33.41  
% 43.48/33.41  Simplification rules
% 43.48/33.41  ----------------------
% 43.48/33.41  #Subsume      : 416
% 43.48/33.41  #Demod        : 42930
% 43.48/33.41  #Tautology    : 8522
% 43.48/33.41  #SimpNegUnit  : 0
% 43.48/33.41  #BackRed      : 79
% 43.48/33.41  
% 43.48/33.41  #Partial instantiations: 0
% 43.48/33.41  #Strategies tried      : 1
% 43.48/33.41  
% 43.48/33.41  Timing (in seconds)
% 43.48/33.41  ----------------------
% 43.48/33.42  Preprocessing        : 0.27
% 43.48/33.42  Parsing              : 0.15
% 43.48/33.42  CNF conversion       : 0.02
% 43.48/33.42  Main loop            : 32.37
% 43.48/33.42  Inferencing          : 2.11
% 43.56/33.42  Reduction            : 22.18
% 43.56/33.42  Demodulation         : 21.06
% 43.56/33.42  BG Simplification    : 0.47
% 43.56/33.42  Subsumption          : 6.40
% 43.56/33.42  Abstraction          : 0.67
% 43.56/33.42  MUC search           : 0.00
% 43.56/33.42  Cooper               : 0.00
% 43.56/33.42  Total                : 32.68
% 43.56/33.42  Index Insertion      : 0.00
% 43.56/33.42  Index Deletion       : 0.00
% 43.56/33.42  Index Matching       : 0.00
% 43.56/33.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
