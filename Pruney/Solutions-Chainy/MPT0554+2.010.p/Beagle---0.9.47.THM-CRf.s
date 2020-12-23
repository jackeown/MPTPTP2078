%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:04 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   40 (  81 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 182 expanded)
%              Number of equality atoms :    3 (  13 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k7_relat_1(A_3,B_4))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [C_7,A_5,D_9,B_6] :
      ( r1_tarski(k7_relat_1(C_7,A_5),k7_relat_1(D_9,B_6))
      | ~ r1_tarski(A_5,B_6)
      | ~ r1_tarski(C_7,D_9)
      | ~ v1_relat_1(D_9)
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k2_relat_1(A_24),k2_relat_1(B_25))
      | ~ r1_tarski(A_24,B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_147,plain,(
    ! [B_41,A_42,B_43] :
      ( r1_tarski(k9_relat_1(B_41,A_42),k2_relat_1(B_43))
      | ~ r1_tarski(k7_relat_1(B_41,A_42),B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(k7_relat_1(B_41,A_42))
      | ~ v1_relat_1(B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_50])).

tff(c_336,plain,(
    ! [B_86,A_87,B_88,A_89] :
      ( r1_tarski(k9_relat_1(B_86,A_87),k9_relat_1(B_88,A_89))
      | ~ r1_tarski(k7_relat_1(B_86,A_87),k7_relat_1(B_88,A_89))
      | ~ v1_relat_1(k7_relat_1(B_88,A_89))
      | ~ v1_relat_1(k7_relat_1(B_86,A_87))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_147])).

tff(c_18,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_349,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_336,c_18])).

tff(c_357,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_349])).

tff(c_358,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_361,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_358])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_361])).

tff(c_366,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_368,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_371,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_368])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_20,c_371])).

tff(c_376,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_380,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_376])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:02:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.39  
% 2.62/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.39  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.39  
% 2.62/1.39  %Foreground sorts:
% 2.62/1.39  
% 2.62/1.39  
% 2.62/1.39  %Background operators:
% 2.62/1.39  
% 2.62/1.39  
% 2.62/1.39  %Foreground operators:
% 2.62/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.62/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.62/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.39  
% 2.62/1.40  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 2.62/1.40  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.62/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.62/1.40  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 2.62/1.40  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.62/1.40  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.62/1.40  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.62/1.40  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k7_relat_1(A_3, B_4)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.40  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.62/1.40  tff(c_10, plain, (![C_7, A_5, D_9, B_6]: (r1_tarski(k7_relat_1(C_7, A_5), k7_relat_1(D_9, B_6)) | ~r1_tarski(A_5, B_6) | ~r1_tarski(C_7, D_9) | ~v1_relat_1(D_9) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.62/1.40  tff(c_12, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.62/1.40  tff(c_50, plain, (![A_24, B_25]: (r1_tarski(k2_relat_1(A_24), k2_relat_1(B_25)) | ~r1_tarski(A_24, B_25) | ~v1_relat_1(B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.62/1.40  tff(c_147, plain, (![B_41, A_42, B_43]: (r1_tarski(k9_relat_1(B_41, A_42), k2_relat_1(B_43)) | ~r1_tarski(k7_relat_1(B_41, A_42), B_43) | ~v1_relat_1(B_43) | ~v1_relat_1(k7_relat_1(B_41, A_42)) | ~v1_relat_1(B_41))), inference(superposition, [status(thm), theory('equality')], [c_12, c_50])).
% 2.62/1.40  tff(c_336, plain, (![B_86, A_87, B_88, A_89]: (r1_tarski(k9_relat_1(B_86, A_87), k9_relat_1(B_88, A_89)) | ~r1_tarski(k7_relat_1(B_86, A_87), k7_relat_1(B_88, A_89)) | ~v1_relat_1(k7_relat_1(B_88, A_89)) | ~v1_relat_1(k7_relat_1(B_86, A_87)) | ~v1_relat_1(B_86) | ~v1_relat_1(B_88))), inference(superposition, [status(thm), theory('equality')], [c_12, c_147])).
% 2.62/1.40  tff(c_18, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.62/1.40  tff(c_349, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_336, c_18])).
% 2.62/1.40  tff(c_357, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_349])).
% 2.62/1.40  tff(c_358, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_357])).
% 2.62/1.40  tff(c_361, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_358])).
% 2.62/1.40  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_361])).
% 2.62/1.40  tff(c_366, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_357])).
% 2.62/1.40  tff(c_368, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_366])).
% 2.62/1.40  tff(c_371, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_368])).
% 2.62/1.40  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_20, c_371])).
% 2.62/1.40  tff(c_376, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_366])).
% 2.62/1.40  tff(c_380, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_376])).
% 2.62/1.40  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_380])).
% 2.62/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.40  
% 2.62/1.40  Inference rules
% 2.62/1.40  ----------------------
% 2.62/1.40  #Ref     : 0
% 2.62/1.40  #Sup     : 82
% 2.62/1.40  #Fact    : 0
% 2.62/1.40  #Define  : 0
% 2.62/1.40  #Split   : 3
% 2.62/1.40  #Chain   : 0
% 2.62/1.40  #Close   : 0
% 2.62/1.40  
% 2.62/1.40  Ordering : KBO
% 2.62/1.40  
% 2.62/1.40  Simplification rules
% 2.62/1.40  ----------------------
% 2.62/1.40  #Subsume      : 9
% 2.62/1.40  #Demod        : 21
% 2.62/1.40  #Tautology    : 14
% 2.62/1.40  #SimpNegUnit  : 0
% 2.62/1.40  #BackRed      : 0
% 2.62/1.40  
% 2.62/1.40  #Partial instantiations: 0
% 2.62/1.40  #Strategies tried      : 1
% 2.62/1.40  
% 2.62/1.40  Timing (in seconds)
% 2.62/1.40  ----------------------
% 2.62/1.40  Preprocessing        : 0.26
% 2.62/1.40  Parsing              : 0.14
% 2.62/1.40  CNF conversion       : 0.02
% 2.62/1.40  Main loop            : 0.32
% 2.62/1.40  Inferencing          : 0.12
% 2.62/1.40  Reduction            : 0.07
% 2.62/1.40  Demodulation         : 0.05
% 2.62/1.40  BG Simplification    : 0.02
% 2.62/1.40  Subsumption          : 0.09
% 2.62/1.40  Abstraction          : 0.02
% 2.62/1.40  MUC search           : 0.00
% 2.62/1.40  Cooper               : 0.00
% 2.62/1.40  Total                : 0.61
% 2.62/1.40  Index Insertion      : 0.00
% 2.62/1.40  Index Deletion       : 0.00
% 2.62/1.40  Index Matching       : 0.00
% 2.62/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
