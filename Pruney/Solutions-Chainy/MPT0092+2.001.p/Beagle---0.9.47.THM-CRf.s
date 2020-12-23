%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:28 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   43 (  62 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  61 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_139])).

tff(c_289,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_327,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_289])).

tff(c_336,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_327])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_139])).

tff(c_616,plain,(
    ! [A_59,B_60] : k4_xboole_0(k3_xboole_0(A_59,B_60),A_59) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_150])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k3_xboole_0(A_18,B_19),C_20) = k3_xboole_0(A_18,k4_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_779,plain,(
    ! [A_64,B_65] : k3_xboole_0(A_64,k4_xboole_0(B_65,A_64)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_22])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_800,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k4_xboole_0(B_65,A_64)) = k4_xboole_0(A_64,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_18])).

tff(c_898,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(B_69,A_68)) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_800])).

tff(c_543,plain,(
    ! [A_56,B_57,C_58] : k4_xboole_0(k3_xboole_0(A_56,B_57),C_58) = k3_xboole_0(A_56,k4_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_593,plain,(
    ! [C_58] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_58)) = k4_xboole_0('#skF_1',C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_543])).

tff(c_911,plain,(
    ! [B_69] : k4_xboole_0('#skF_1',k4_xboole_0(B_69,'#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_898,c_593])).

tff(c_985,plain,(
    ! [B_69] : k4_xboole_0('#skF_1',k4_xboole_0(B_69,'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_911])).

tff(c_280,plain,(
    ! [A_42,B_43] :
      ( r1_xboole_0(A_42,B_43)
      | k4_xboole_0(A_42,B_43) != A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_288,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_280,c_28])).

tff(c_1808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:39:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.51  
% 3.02/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.51  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.02/1.51  
% 3.02/1.51  %Foreground sorts:
% 3.02/1.51  
% 3.02/1.51  
% 3.02/1.51  %Background operators:
% 3.02/1.51  
% 3.02/1.51  
% 3.02/1.51  %Foreground operators:
% 3.02/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.02/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.51  
% 3.02/1.52  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.02/1.52  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.02/1.52  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.02/1.52  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.02/1.52  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.02/1.52  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.02/1.52  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.02/1.52  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.02/1.52  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.02/1.52  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.02/1.52  tff(c_139, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.02/1.52  tff(c_151, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_139])).
% 3.02/1.52  tff(c_289, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.02/1.52  tff(c_327, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_151, c_289])).
% 3.02/1.52  tff(c_336, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_327])).
% 3.02/1.52  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.52  tff(c_150, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_139])).
% 3.02/1.52  tff(c_616, plain, (![A_59, B_60]: (k4_xboole_0(k3_xboole_0(A_59, B_60), A_59)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_289, c_150])).
% 3.02/1.52  tff(c_22, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k3_xboole_0(A_18, B_19), C_20)=k3_xboole_0(A_18, k4_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.52  tff(c_779, plain, (![A_64, B_65]: (k3_xboole_0(A_64, k4_xboole_0(B_65, A_64))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_616, c_22])).
% 3.02/1.52  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.02/1.52  tff(c_800, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k4_xboole_0(B_65, A_64))=k4_xboole_0(A_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_779, c_18])).
% 3.02/1.52  tff(c_898, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(B_69, A_68))=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_800])).
% 3.02/1.52  tff(c_543, plain, (![A_56, B_57, C_58]: (k4_xboole_0(k3_xboole_0(A_56, B_57), C_58)=k3_xboole_0(A_56, k4_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.52  tff(c_593, plain, (![C_58]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_58))=k4_xboole_0('#skF_1', C_58))), inference(superposition, [status(thm), theory('equality')], [c_336, c_543])).
% 3.02/1.52  tff(c_911, plain, (![B_69]: (k4_xboole_0('#skF_1', k4_xboole_0(B_69, '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_898, c_593])).
% 3.02/1.52  tff(c_985, plain, (![B_69]: (k4_xboole_0('#skF_1', k4_xboole_0(B_69, '#skF_2'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_336, c_911])).
% 3.02/1.52  tff(c_280, plain, (![A_42, B_43]: (r1_xboole_0(A_42, B_43) | k4_xboole_0(A_42, B_43)!=A_42)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.02/1.52  tff(c_28, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.02/1.52  tff(c_288, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))!='#skF_1'), inference(resolution, [status(thm)], [c_280, c_28])).
% 3.02/1.52  tff(c_1808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_985, c_288])).
% 3.02/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.52  
% 3.02/1.52  Inference rules
% 3.02/1.52  ----------------------
% 3.02/1.52  #Ref     : 0
% 3.02/1.52  #Sup     : 433
% 3.02/1.52  #Fact    : 0
% 3.02/1.52  #Define  : 0
% 3.02/1.52  #Split   : 0
% 3.02/1.52  #Chain   : 0
% 3.02/1.52  #Close   : 0
% 3.02/1.52  
% 3.02/1.52  Ordering : KBO
% 3.02/1.52  
% 3.02/1.52  Simplification rules
% 3.02/1.52  ----------------------
% 3.02/1.52  #Subsume      : 0
% 3.02/1.52  #Demod        : 294
% 3.02/1.52  #Tautology    : 321
% 3.02/1.52  #SimpNegUnit  : 0
% 3.02/1.52  #BackRed      : 1
% 3.02/1.52  
% 3.02/1.52  #Partial instantiations: 0
% 3.02/1.52  #Strategies tried      : 1
% 3.02/1.52  
% 3.02/1.52  Timing (in seconds)
% 3.02/1.52  ----------------------
% 3.02/1.52  Preprocessing        : 0.30
% 3.02/1.52  Parsing              : 0.16
% 3.02/1.52  CNF conversion       : 0.02
% 3.02/1.52  Main loop            : 0.45
% 3.02/1.52  Inferencing          : 0.16
% 3.02/1.52  Reduction            : 0.18
% 3.02/1.52  Demodulation         : 0.14
% 3.02/1.52  BG Simplification    : 0.02
% 3.02/1.52  Subsumption          : 0.06
% 3.02/1.52  Abstraction          : 0.03
% 3.02/1.52  MUC search           : 0.00
% 3.02/1.52  Cooper               : 0.00
% 3.02/1.52  Total                : 0.78
% 3.02/1.52  Index Insertion      : 0.00
% 3.02/1.53  Index Deletion       : 0.00
% 3.02/1.53  Index Matching       : 0.00
% 3.02/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
