%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:45 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   47 (  72 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  71 expanded)
%              Number of equality atoms :   31 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_94,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_56,plain,(
    ! [A_54] : k3_tarski(k1_tarski(A_54)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_139,plain,(
    ! [A_72,B_73] : k3_tarski(k2_tarski(A_72,B_73)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_148,plain,(
    ! [A_17] : k3_tarski(k1_tarski(A_17)) = k2_xboole_0(A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_139])).

tff(c_151,plain,(
    ! [A_17] : k2_xboole_0(A_17,A_17) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_148])).

tff(c_52,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(k1_tarski(A_50),k1_tarski(B_51))
      | B_51 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_263,plain,(
    ! [A_90,B_91] :
      ( k4_xboole_0(A_90,B_91) = A_90
      | ~ r1_xboole_0(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_671,plain,(
    ! [A_136,B_137] :
      ( k4_xboole_0(k1_tarski(A_136),k1_tarski(B_137)) = k1_tarski(A_136)
      | B_137 = A_136 ) ),
    inference(resolution,[status(thm)],[c_52,c_263])).

tff(c_24,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_835,plain,(
    ! [B_167,A_168] :
      ( k5_xboole_0(k1_tarski(B_167),k1_tarski(A_168)) = k2_xboole_0(k1_tarski(B_167),k1_tarski(A_168))
      | B_167 = A_168 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_24])).

tff(c_54,plain,(
    ! [A_52,B_53] :
      ( k5_xboole_0(k1_tarski(A_52),k1_tarski(B_53)) = k2_tarski(A_52,B_53)
      | B_53 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1057,plain,(
    ! [B_184,A_185] :
      ( k2_xboole_0(k1_tarski(B_184),k1_tarski(A_185)) = k2_tarski(B_184,A_185)
      | B_184 = A_185
      | B_184 = A_185 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_54])).

tff(c_50,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_58,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_59,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_58])).

tff(c_1078,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1057,c_59])).

tff(c_1082,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1078,c_1078,c_59])).

tff(c_1085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_26,c_1082])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:12:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.54  
% 3.12/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.54  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.12/1.54  
% 3.12/1.54  %Foreground sorts:
% 3.12/1.54  
% 3.12/1.54  
% 3.12/1.54  %Background operators:
% 3.12/1.54  
% 3.12/1.54  
% 3.12/1.54  %Foreground operators:
% 3.12/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.12/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.12/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.12/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.12/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.12/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.54  
% 3.12/1.55  tff(f_94, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 3.12/1.55  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.12/1.55  tff(f_82, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.12/1.55  tff(f_87, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.12/1.55  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.12/1.55  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.12/1.55  tff(f_92, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 3.12/1.55  tff(f_97, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 3.12/1.55  tff(c_56, plain, (![A_54]: (k3_tarski(k1_tarski(A_54))=A_54)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.12/1.55  tff(c_26, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.12/1.55  tff(c_139, plain, (![A_72, B_73]: (k3_tarski(k2_tarski(A_72, B_73))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.12/1.55  tff(c_148, plain, (![A_17]: (k3_tarski(k1_tarski(A_17))=k2_xboole_0(A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_26, c_139])).
% 3.12/1.55  tff(c_151, plain, (![A_17]: (k2_xboole_0(A_17, A_17)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_148])).
% 3.12/1.55  tff(c_52, plain, (![A_50, B_51]: (r1_xboole_0(k1_tarski(A_50), k1_tarski(B_51)) | B_51=A_50)), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.12/1.55  tff(c_263, plain, (![A_90, B_91]: (k4_xboole_0(A_90, B_91)=A_90 | ~r1_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.12/1.55  tff(c_671, plain, (![A_136, B_137]: (k4_xboole_0(k1_tarski(A_136), k1_tarski(B_137))=k1_tarski(A_136) | B_137=A_136)), inference(resolution, [status(thm)], [c_52, c_263])).
% 3.12/1.55  tff(c_24, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.12/1.55  tff(c_835, plain, (![B_167, A_168]: (k5_xboole_0(k1_tarski(B_167), k1_tarski(A_168))=k2_xboole_0(k1_tarski(B_167), k1_tarski(A_168)) | B_167=A_168)), inference(superposition, [status(thm), theory('equality')], [c_671, c_24])).
% 3.12/1.55  tff(c_54, plain, (![A_52, B_53]: (k5_xboole_0(k1_tarski(A_52), k1_tarski(B_53))=k2_tarski(A_52, B_53) | B_53=A_52)), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.12/1.55  tff(c_1057, plain, (![B_184, A_185]: (k2_xboole_0(k1_tarski(B_184), k1_tarski(A_185))=k2_tarski(B_184, A_185) | B_184=A_185 | B_184=A_185)), inference(superposition, [status(thm), theory('equality')], [c_835, c_54])).
% 3.12/1.55  tff(c_50, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.12/1.55  tff(c_58, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.12/1.55  tff(c_59, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_58])).
% 3.12/1.55  tff(c_1078, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1057, c_59])).
% 3.12/1.55  tff(c_1082, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1078, c_1078, c_59])).
% 3.12/1.55  tff(c_1085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_26, c_1082])).
% 3.12/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.55  
% 3.12/1.55  Inference rules
% 3.12/1.55  ----------------------
% 3.12/1.55  #Ref     : 0
% 3.12/1.55  #Sup     : 236
% 3.12/1.55  #Fact    : 0
% 3.12/1.55  #Define  : 0
% 3.12/1.55  #Split   : 0
% 3.12/1.55  #Chain   : 0
% 3.12/1.55  #Close   : 0
% 3.12/1.55  
% 3.12/1.55  Ordering : KBO
% 3.12/1.55  
% 3.12/1.55  Simplification rules
% 3.12/1.55  ----------------------
% 3.12/1.55  #Subsume      : 9
% 3.12/1.55  #Demod        : 105
% 3.12/1.55  #Tautology    : 174
% 3.12/1.55  #SimpNegUnit  : 0
% 3.12/1.55  #BackRed      : 1
% 3.12/1.55  
% 3.12/1.55  #Partial instantiations: 0
% 3.12/1.55  #Strategies tried      : 1
% 3.12/1.55  
% 3.12/1.55  Timing (in seconds)
% 3.12/1.55  ----------------------
% 3.12/1.56  Preprocessing        : 0.36
% 3.12/1.56  Parsing              : 0.19
% 3.12/1.56  CNF conversion       : 0.02
% 3.12/1.56  Main loop            : 0.39
% 3.12/1.56  Inferencing          : 0.16
% 3.12/1.56  Reduction            : 0.13
% 3.12/1.56  Demodulation         : 0.09
% 3.12/1.56  BG Simplification    : 0.02
% 3.12/1.56  Subsumption          : 0.06
% 3.12/1.56  Abstraction          : 0.02
% 3.12/1.56  MUC search           : 0.00
% 3.12/1.56  Cooper               : 0.00
% 3.12/1.56  Total                : 0.77
% 3.12/1.56  Index Insertion      : 0.00
% 3.12/1.56  Index Deletion       : 0.00
% 3.12/1.56  Index Matching       : 0.00
% 3.12/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
