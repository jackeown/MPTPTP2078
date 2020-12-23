%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:47 EST 2020

% Result     : Theorem 5.19s
% Output     : CNFRefutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  74 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  71 expanded)
%              Number of equality atoms :   31 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_46,plain,(
    ! [A_53] : k3_tarski(k1_tarski(A_53)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_133,plain,(
    ! [A_72,B_73] : k3_tarski(k2_tarski(A_72,B_73)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_142,plain,(
    ! [A_24] : k3_tarski(k1_tarski(A_24)) = k2_xboole_0(A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_133])).

tff(c_145,plain,(
    ! [A_24] : k2_xboole_0(A_24,A_24) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_142])).

tff(c_44,plain,(
    ! [A_51,B_52] :
      ( k5_xboole_0(k1_tarski(A_51),k1_tarski(B_52)) = k2_tarski(A_51,B_52)
      | B_52 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_123,plain,(
    ! [A_68,B_69] :
      ( r1_xboole_0(k1_tarski(A_68),k1_tarski(B_69))
      | B_69 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1052,plain,(
    ! [A_152,B_153] :
      ( k4_xboole_0(k1_tarski(A_152),k1_tarski(B_153)) = k1_tarski(A_152)
      | B_153 = A_152 ) ),
    inference(resolution,[status(thm)],[c_123,c_20])).

tff(c_24,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3592,plain,(
    ! [B_235,A_236] :
      ( k5_xboole_0(k1_tarski(B_235),k1_tarski(A_236)) = k2_xboole_0(k1_tarski(B_235),k1_tarski(A_236))
      | B_235 = A_236 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_24])).

tff(c_5482,plain,(
    ! [A_269,B_270] :
      ( k2_xboole_0(k1_tarski(A_269),k1_tarski(B_270)) = k2_tarski(A_269,B_270)
      | B_270 = A_269
      | B_270 = A_269 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_3592])).

tff(c_38,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_49,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_5503,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5482,c_49])).

tff(c_5507,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5503,c_5503,c_49])).

tff(c_5510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_26,c_5507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.19/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/2.02  
% 5.19/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/2.02  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.19/2.02  
% 5.19/2.02  %Foreground sorts:
% 5.19/2.02  
% 5.19/2.02  
% 5.19/2.02  %Background operators:
% 5.19/2.02  
% 5.19/2.02  
% 5.19/2.02  %Foreground operators:
% 5.19/2.02  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.19/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.19/2.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.19/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.19/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.19/2.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.19/2.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.19/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.19/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.19/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.19/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.19/2.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.19/2.02  tff('#skF_3', type, '#skF_3': $i).
% 5.19/2.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.19/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/2.02  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.19/2.02  tff('#skF_4', type, '#skF_4': $i).
% 5.19/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.19/2.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.19/2.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.19/2.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.19/2.02  
% 5.19/2.03  tff(f_95, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 5.19/2.03  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.19/2.03  tff(f_81, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.19/2.03  tff(f_93, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 5.19/2.03  tff(f_86, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 5.19/2.03  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.19/2.03  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.19/2.03  tff(f_98, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 5.19/2.03  tff(c_46, plain, (![A_53]: (k3_tarski(k1_tarski(A_53))=A_53)), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.19/2.03  tff(c_26, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.19/2.03  tff(c_133, plain, (![A_72, B_73]: (k3_tarski(k2_tarski(A_72, B_73))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.19/2.03  tff(c_142, plain, (![A_24]: (k3_tarski(k1_tarski(A_24))=k2_xboole_0(A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_26, c_133])).
% 5.19/2.03  tff(c_145, plain, (![A_24]: (k2_xboole_0(A_24, A_24)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_142])).
% 5.19/2.03  tff(c_44, plain, (![A_51, B_52]: (k5_xboole_0(k1_tarski(A_51), k1_tarski(B_52))=k2_tarski(A_51, B_52) | B_52=A_51)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.19/2.03  tff(c_123, plain, (![A_68, B_69]: (r1_xboole_0(k1_tarski(A_68), k1_tarski(B_69)) | B_69=A_68)), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.19/2.03  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.19/2.03  tff(c_1052, plain, (![A_152, B_153]: (k4_xboole_0(k1_tarski(A_152), k1_tarski(B_153))=k1_tarski(A_152) | B_153=A_152)), inference(resolution, [status(thm)], [c_123, c_20])).
% 5.19/2.03  tff(c_24, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.19/2.03  tff(c_3592, plain, (![B_235, A_236]: (k5_xboole_0(k1_tarski(B_235), k1_tarski(A_236))=k2_xboole_0(k1_tarski(B_235), k1_tarski(A_236)) | B_235=A_236)), inference(superposition, [status(thm), theory('equality')], [c_1052, c_24])).
% 5.19/2.03  tff(c_5482, plain, (![A_269, B_270]: (k2_xboole_0(k1_tarski(A_269), k1_tarski(B_270))=k2_tarski(A_269, B_270) | B_270=A_269 | B_270=A_269)), inference(superposition, [status(thm), theory('equality')], [c_44, c_3592])).
% 5.19/2.03  tff(c_38, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.19/2.03  tff(c_48, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4')))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.19/2.03  tff(c_49, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48])).
% 5.19/2.03  tff(c_5503, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5482, c_49])).
% 5.19/2.03  tff(c_5507, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5503, c_5503, c_49])).
% 5.19/2.03  tff(c_5510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_26, c_5507])).
% 5.19/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/2.03  
% 5.19/2.03  Inference rules
% 5.19/2.03  ----------------------
% 5.19/2.03  #Ref     : 0
% 5.19/2.03  #Sup     : 1285
% 5.19/2.03  #Fact    : 0
% 5.19/2.03  #Define  : 0
% 5.19/2.03  #Split   : 0
% 5.19/2.03  #Chain   : 0
% 5.19/2.03  #Close   : 0
% 5.19/2.03  
% 5.19/2.03  Ordering : KBO
% 5.19/2.03  
% 5.19/2.03  Simplification rules
% 5.19/2.03  ----------------------
% 5.19/2.03  #Subsume      : 270
% 5.19/2.03  #Demod        : 1136
% 5.19/2.03  #Tautology    : 772
% 5.19/2.03  #SimpNegUnit  : 34
% 5.19/2.03  #BackRed      : 3
% 5.19/2.03  
% 5.19/2.03  #Partial instantiations: 0
% 5.19/2.03  #Strategies tried      : 1
% 5.19/2.03  
% 5.19/2.03  Timing (in seconds)
% 5.19/2.03  ----------------------
% 5.43/2.03  Preprocessing        : 0.34
% 5.43/2.03  Parsing              : 0.18
% 5.43/2.03  CNF conversion       : 0.02
% 5.43/2.03  Main loop            : 0.93
% 5.43/2.03  Inferencing          : 0.30
% 5.43/2.03  Reduction            : 0.38
% 5.43/2.03  Demodulation         : 0.30
% 5.43/2.03  BG Simplification    : 0.04
% 5.43/2.03  Subsumption          : 0.15
% 5.43/2.03  Abstraction          : 0.05
% 5.43/2.03  MUC search           : 0.00
% 5.43/2.03  Cooper               : 0.00
% 5.43/2.04  Total                : 1.29
% 5.43/2.04  Index Insertion      : 0.00
% 5.43/2.04  Index Deletion       : 0.00
% 5.43/2.04  Index Matching       : 0.00
% 5.43/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
