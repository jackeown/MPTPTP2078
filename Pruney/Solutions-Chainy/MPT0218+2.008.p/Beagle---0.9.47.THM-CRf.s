%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:47 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_16,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k2_enumset1(A_16,A_16,B_17,C_18) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_109,plain,(
    ! [A_55,B_56,C_57,D_58] : k2_xboole_0(k2_tarski(A_55,B_56),k2_tarski(C_57,D_58)) = k2_enumset1(A_55,B_56,C_57,D_58) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [A_59,B_60,C_61,D_62] : k4_xboole_0(k2_tarski(A_59,B_60),k2_enumset1(A_59,B_60,C_61,D_62)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_10])).

tff(c_138,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k2_tarski(A_16,A_16),k1_enumset1(A_16,B_17,C_18)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_131])).

tff(c_146,plain,(
    ! [A_63,B_64,C_65] : k4_xboole_0(k1_tarski(A_63),k1_enumset1(A_63,B_64,C_65)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_138])).

tff(c_153,plain,(
    ! [A_14,B_15] : k4_xboole_0(k1_tarski(A_14),k2_tarski(A_14,B_15)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_146])).

tff(c_52,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | k4_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_26])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:01:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.11  
% 1.68/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.12  %$ r1_tarski > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.68/1.12  
% 1.68/1.12  %Foreground sorts:
% 1.68/1.12  
% 1.68/1.12  
% 1.68/1.12  %Background operators:
% 1.68/1.12  
% 1.68/1.12  
% 1.68/1.12  %Foreground operators:
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.68/1.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.68/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.68/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.68/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.12  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.68/1.12  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.12  
% 1.68/1.13  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.68/1.13  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.68/1.13  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.68/1.13  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 1.68/1.13  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.68/1.13  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.68/1.13  tff(f_52, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.68/1.13  tff(c_16, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.68/1.13  tff(c_14, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.68/1.13  tff(c_18, plain, (![A_16, B_17, C_18]: (k2_enumset1(A_16, A_16, B_17, C_18)=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.68/1.13  tff(c_109, plain, (![A_55, B_56, C_57, D_58]: (k2_xboole_0(k2_tarski(A_55, B_56), k2_tarski(C_57, D_58))=k2_enumset1(A_55, B_56, C_57, D_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.68/1.13  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.68/1.13  tff(c_131, plain, (![A_59, B_60, C_61, D_62]: (k4_xboole_0(k2_tarski(A_59, B_60), k2_enumset1(A_59, B_60, C_61, D_62))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_109, c_10])).
% 1.68/1.13  tff(c_138, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k2_tarski(A_16, A_16), k1_enumset1(A_16, B_17, C_18))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_131])).
% 1.68/1.13  tff(c_146, plain, (![A_63, B_64, C_65]: (k4_xboole_0(k1_tarski(A_63), k1_enumset1(A_63, B_64, C_65))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_138])).
% 1.68/1.13  tff(c_153, plain, (![A_14, B_15]: (k4_xboole_0(k1_tarski(A_14), k2_tarski(A_14, B_15))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_146])).
% 1.68/1.13  tff(c_52, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | k4_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.13  tff(c_26, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.68/1.13  tff(c_56, plain, (k4_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_26])).
% 1.68/1.13  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153, c_56])).
% 1.68/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  Inference rules
% 1.68/1.13  ----------------------
% 1.68/1.13  #Ref     : 0
% 1.68/1.13  #Sup     : 34
% 1.68/1.13  #Fact    : 0
% 1.68/1.13  #Define  : 0
% 1.68/1.13  #Split   : 0
% 1.68/1.13  #Chain   : 0
% 1.68/1.13  #Close   : 0
% 1.68/1.13  
% 1.68/1.13  Ordering : KBO
% 1.68/1.13  
% 1.68/1.13  Simplification rules
% 1.68/1.13  ----------------------
% 1.68/1.13  #Subsume      : 0
% 1.68/1.13  #Demod        : 5
% 1.68/1.13  #Tautology    : 25
% 1.68/1.13  #SimpNegUnit  : 0
% 1.68/1.13  #BackRed      : 1
% 1.68/1.13  
% 1.68/1.13  #Partial instantiations: 0
% 1.68/1.13  #Strategies tried      : 1
% 1.68/1.13  
% 1.68/1.13  Timing (in seconds)
% 1.68/1.13  ----------------------
% 1.68/1.13  Preprocessing        : 0.28
% 1.68/1.13  Parsing              : 0.15
% 1.68/1.13  CNF conversion       : 0.02
% 1.68/1.13  Main loop            : 0.11
% 1.68/1.13  Inferencing          : 0.05
% 1.68/1.13  Reduction            : 0.04
% 1.68/1.13  Demodulation         : 0.03
% 1.68/1.13  BG Simplification    : 0.01
% 1.68/1.13  Subsumption          : 0.01
% 1.68/1.13  Abstraction          : 0.01
% 1.68/1.13  MUC search           : 0.00
% 1.68/1.13  Cooper               : 0.00
% 1.68/1.13  Total                : 0.41
% 1.68/1.13  Index Insertion      : 0.00
% 1.68/1.13  Index Deletion       : 0.00
% 1.68/1.13  Index Matching       : 0.00
% 1.68/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
