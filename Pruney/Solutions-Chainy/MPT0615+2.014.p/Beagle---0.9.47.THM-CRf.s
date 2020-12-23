%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:50 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   37 (  49 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  90 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_66,plain,(
    r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_16,plain,
    ( ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_94,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_16])).

tff(c_8,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    k2_xboole_0('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) = k7_relat_1('#skF_2',k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_150,plain,(
    ! [C_31] :
      ( r1_tarski('#skF_1',C_31)
      | ~ r1_tarski(k7_relat_1('#skF_2',k1_relat_1('#skF_1')),C_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_2])).

tff(c_166,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_150])).

tff(c_175,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_166])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_175])).

tff(c_178,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_10,plain,(
    ! [A_12] :
      ( k7_relat_1(A_12,k1_relat_1(A_12)) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_339,plain,(
    ! [B_47,A_48,C_49] :
      ( r1_tarski(k7_relat_1(B_47,A_48),k7_relat_1(C_49,A_48))
      | ~ r1_tarski(B_47,C_49)
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_547,plain,(
    ! [A_63,C_64] :
      ( r1_tarski(A_63,k7_relat_1(C_64,k1_relat_1(A_63)))
      | ~ r1_tarski(A_63,C_64)
      | ~ v1_relat_1(C_64)
      | ~ v1_relat_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_339])).

tff(c_179,plain,(
    ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_556,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_547,c_179])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_178,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:19:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.29  
% 2.13/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.29  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.13/1.29  
% 2.13/1.29  %Foreground sorts:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Background operators:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Foreground operators:
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.13/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.29  
% 2.13/1.30  tff(f_60, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t219_relat_1)).
% 2.13/1.30  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.13/1.30  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.13/1.30  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.13/1.30  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.13/1.30  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 2.13/1.30  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.30  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.30  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2') | r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.30  tff(c_66, plain, (r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_22])).
% 2.13/1.30  tff(c_16, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1'))) | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.30  tff(c_94, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_16])).
% 2.13/1.30  tff(c_8, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.30  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.30  tff(c_77, plain, (k2_xboole_0('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))=k7_relat_1('#skF_2', k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_4])).
% 2.13/1.30  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.30  tff(c_150, plain, (![C_31]: (r1_tarski('#skF_1', C_31) | ~r1_tarski(k7_relat_1('#skF_2', k1_relat_1('#skF_1')), C_31))), inference(superposition, [status(thm), theory('equality')], [c_77, c_2])).
% 2.13/1.30  tff(c_166, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_150])).
% 2.13/1.30  tff(c_175, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_166])).
% 2.13/1.30  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_175])).
% 2.13/1.30  tff(c_178, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 2.13/1.30  tff(c_10, plain, (![A_12]: (k7_relat_1(A_12, k1_relat_1(A_12))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.30  tff(c_339, plain, (![B_47, A_48, C_49]: (r1_tarski(k7_relat_1(B_47, A_48), k7_relat_1(C_49, A_48)) | ~r1_tarski(B_47, C_49) | ~v1_relat_1(C_49) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.13/1.30  tff(c_547, plain, (![A_63, C_64]: (r1_tarski(A_63, k7_relat_1(C_64, k1_relat_1(A_63))) | ~r1_tarski(A_63, C_64) | ~v1_relat_1(C_64) | ~v1_relat_1(A_63) | ~v1_relat_1(A_63))), inference(superposition, [status(thm), theory('equality')], [c_10, c_339])).
% 2.13/1.30  tff(c_179, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitRight, [status(thm)], [c_22])).
% 2.13/1.30  tff(c_556, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_547, c_179])).
% 2.13/1.30  tff(c_574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_178, c_556])).
% 2.13/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  Inference rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Ref     : 0
% 2.13/1.30  #Sup     : 131
% 2.13/1.30  #Fact    : 0
% 2.13/1.30  #Define  : 0
% 2.13/1.30  #Split   : 1
% 2.13/1.30  #Chain   : 0
% 2.13/1.30  #Close   : 0
% 2.13/1.30  
% 2.13/1.30  Ordering : KBO
% 2.13/1.30  
% 2.13/1.30  Simplification rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Subsume      : 15
% 2.13/1.30  #Demod        : 70
% 2.13/1.30  #Tautology    : 52
% 2.13/1.30  #SimpNegUnit  : 1
% 2.13/1.30  #BackRed      : 0
% 2.13/1.30  
% 2.13/1.30  #Partial instantiations: 0
% 2.13/1.30  #Strategies tried      : 1
% 2.13/1.30  
% 2.13/1.30  Timing (in seconds)
% 2.13/1.30  ----------------------
% 2.13/1.31  Preprocessing        : 0.26
% 2.13/1.31  Parsing              : 0.15
% 2.13/1.31  CNF conversion       : 0.02
% 2.13/1.31  Main loop            : 0.29
% 2.13/1.31  Inferencing          : 0.12
% 2.13/1.31  Reduction            : 0.07
% 2.13/1.31  Demodulation         : 0.05
% 2.13/1.31  BG Simplification    : 0.01
% 2.13/1.31  Subsumption          : 0.06
% 2.13/1.31  Abstraction          : 0.01
% 2.13/1.31  MUC search           : 0.00
% 2.13/1.31  Cooper               : 0.00
% 2.13/1.31  Total                : 0.57
% 2.13/1.31  Index Insertion      : 0.00
% 2.13/1.31  Index Deletion       : 0.00
% 2.13/1.31  Index Matching       : 0.00
% 2.13/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
