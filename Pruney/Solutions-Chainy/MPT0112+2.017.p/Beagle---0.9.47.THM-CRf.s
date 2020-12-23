%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:11 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   44 (  71 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   35 (  63 expanded)
%              Number of equality atoms :   24 (  51 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_18,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    ! [B_18,A_19] :
      ( ~ r2_xboole_0(B_18,A_19)
      | ~ r1_tarski(A_19,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_50])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k5_xboole_0(k5_xboole_0(A_8,B_9),C_10) = k5_xboole_0(A_8,k5_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,(
    ! [A_25,B_26] : k5_xboole_0(k5_xboole_0(A_25,B_26),k2_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1249,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k5_xboole_0(B_51,k2_xboole_0(A_50,B_51))) = k3_xboole_0(A_50,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_116])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,(
    ! [A_22,B_23,C_24] : k5_xboole_0(k5_xboole_0(A_22,B_23),C_24) = k5_xboole_0(A_22,k5_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_467,plain,(
    ! [A_34,C_35] : k5_xboole_0(A_34,k5_xboole_0(A_34,C_35)) = k5_xboole_0(k1_xboole_0,C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_64])).

tff(c_566,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k5_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_467])).

tff(c_591,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_566])).

tff(c_105,plain,(
    ! [A_11,C_24] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_24)) = k5_xboole_0(k1_xboole_0,C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_64])).

tff(c_592,plain,(
    ! [A_11,C_24] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_24)) = C_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_105])).

tff(c_1264,plain,(
    ! [B_51,A_50] : k5_xboole_0(B_51,k2_xboole_0(A_50,B_51)) = k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_592])).

tff(c_1462,plain,(
    ! [B_54,A_55] : k5_xboole_0(B_54,k2_xboole_0(A_55,B_54)) = k4_xboole_0(A_55,B_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1264])).

tff(c_2103,plain,(
    ! [B_71,A_72] : k5_xboole_0(B_71,k4_xboole_0(A_72,B_71)) = k2_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_1462,c_592])).

tff(c_2164,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2103])).

tff(c_2174,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2164])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2184,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2174,c_8])).

tff(c_2190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.50  
% 3.18/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.50  %$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.18/1.50  
% 3.18/1.50  %Foreground sorts:
% 3.18/1.50  
% 3.18/1.50  
% 3.18/1.50  %Background operators:
% 3.18/1.50  
% 3.18/1.50  
% 3.18/1.50  %Foreground operators:
% 3.18/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.18/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.50  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.18/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.18/1.50  
% 3.18/1.51  tff(f_48, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 3.18/1.51  tff(f_34, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 3.18/1.51  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.18/1.51  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.18/1.51  tff(f_38, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.18/1.51  tff(f_42, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.18/1.51  tff(f_40, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.18/1.51  tff(f_36, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.18/1.51  tff(c_18, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.18/1.51  tff(c_50, plain, (![B_18, A_19]: (~r2_xboole_0(B_18, A_19) | ~r1_tarski(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.18/1.51  tff(c_54, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_18, c_50])).
% 3.18/1.51  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.51  tff(c_16, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.18/1.51  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.18/1.51  tff(c_10, plain, (![A_8, B_9, C_10]: (k5_xboole_0(k5_xboole_0(A_8, B_9), C_10)=k5_xboole_0(A_8, k5_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.51  tff(c_116, plain, (![A_25, B_26]: (k5_xboole_0(k5_xboole_0(A_25, B_26), k2_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.18/1.51  tff(c_1249, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k5_xboole_0(B_51, k2_xboole_0(A_50, B_51)))=k3_xboole_0(A_50, B_51))), inference(superposition, [status(thm), theory('equality')], [c_10, c_116])).
% 3.18/1.51  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.18/1.51  tff(c_64, plain, (![A_22, B_23, C_24]: (k5_xboole_0(k5_xboole_0(A_22, B_23), C_24)=k5_xboole_0(A_22, k5_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.51  tff(c_467, plain, (![A_34, C_35]: (k5_xboole_0(A_34, k5_xboole_0(A_34, C_35))=k5_xboole_0(k1_xboole_0, C_35))), inference(superposition, [status(thm), theory('equality')], [c_12, c_64])).
% 3.18/1.51  tff(c_566, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k5_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_467])).
% 3.18/1.51  tff(c_591, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_566])).
% 3.18/1.51  tff(c_105, plain, (![A_11, C_24]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_24))=k5_xboole_0(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_12, c_64])).
% 3.18/1.51  tff(c_592, plain, (![A_11, C_24]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_24))=C_24)), inference(demodulation, [status(thm), theory('equality')], [c_591, c_105])).
% 3.18/1.51  tff(c_1264, plain, (![B_51, A_50]: (k5_xboole_0(B_51, k2_xboole_0(A_50, B_51))=k5_xboole_0(A_50, k3_xboole_0(A_50, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_1249, c_592])).
% 3.18/1.51  tff(c_1462, plain, (![B_54, A_55]: (k5_xboole_0(B_54, k2_xboole_0(A_55, B_54))=k4_xboole_0(A_55, B_54))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1264])).
% 3.18/1.51  tff(c_2103, plain, (![B_71, A_72]: (k5_xboole_0(B_71, k4_xboole_0(A_72, B_71))=k2_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_1462, c_592])).
% 3.18/1.51  tff(c_2164, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_2103])).
% 3.18/1.51  tff(c_2174, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2164])).
% 3.18/1.51  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.18/1.51  tff(c_2184, plain, (r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2174, c_8])).
% 3.18/1.51  tff(c_2190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2184])).
% 3.18/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.51  
% 3.18/1.51  Inference rules
% 3.18/1.51  ----------------------
% 3.18/1.51  #Ref     : 0
% 3.18/1.51  #Sup     : 538
% 3.18/1.51  #Fact    : 0
% 3.18/1.51  #Define  : 0
% 3.18/1.51  #Split   : 0
% 3.18/1.51  #Chain   : 0
% 3.18/1.51  #Close   : 0
% 3.18/1.51  
% 3.18/1.51  Ordering : KBO
% 3.18/1.51  
% 3.18/1.51  Simplification rules
% 3.18/1.51  ----------------------
% 3.18/1.51  #Subsume      : 3
% 3.18/1.51  #Demod        : 340
% 3.18/1.51  #Tautology    : 326
% 3.18/1.51  #SimpNegUnit  : 1
% 3.18/1.51  #BackRed      : 6
% 3.18/1.51  
% 3.18/1.51  #Partial instantiations: 0
% 3.18/1.51  #Strategies tried      : 1
% 3.18/1.51  
% 3.18/1.51  Timing (in seconds)
% 3.18/1.51  ----------------------
% 3.18/1.52  Preprocessing        : 0.26
% 3.18/1.52  Parsing              : 0.15
% 3.18/1.52  CNF conversion       : 0.02
% 3.18/1.52  Main loop            : 0.50
% 3.18/1.52  Inferencing          : 0.19
% 3.18/1.52  Reduction            : 0.19
% 3.18/1.52  Demodulation         : 0.16
% 3.18/1.52  BG Simplification    : 0.03
% 3.18/1.52  Subsumption          : 0.06
% 3.18/1.52  Abstraction          : 0.03
% 3.18/1.52  MUC search           : 0.00
% 3.18/1.52  Cooper               : 0.00
% 3.18/1.52  Total                : 0.79
% 3.18/1.52  Index Insertion      : 0.00
% 3.18/1.52  Index Deletion       : 0.00
% 3.18/1.52  Index Matching       : 0.00
% 3.18/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
