%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:05 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   38 (  79 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 173 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [C_5,A_3,B_4] :
      ( r1_tarski(k7_relat_1(C_5,A_3),k7_relat_1(C_5,B_4))
      | ~ r1_tarski(A_3,B_4)
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_29,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k2_relat_1(A_20),k2_relat_1(B_21))
      | ~ r1_tarski(A_20,B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [B_22,A_23,B_24] :
      ( r1_tarski(k9_relat_1(B_22,A_23),k2_relat_1(B_24))
      | ~ r1_tarski(k7_relat_1(B_22,A_23),B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(k7_relat_1(B_22,A_23))
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_29])).

tff(c_44,plain,(
    ! [B_28,A_29,B_30,A_31] :
      ( r1_tarski(k9_relat_1(B_28,A_29),k9_relat_1(B_30,A_31))
      | ~ r1_tarski(k7_relat_1(B_28,A_29),k7_relat_1(B_30,A_31))
      | ~ v1_relat_1(k7_relat_1(B_30,A_31))
      | ~ v1_relat_1(k7_relat_1(B_28,A_29))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_36])).

tff(c_12,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_47,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_12])).

tff(c_50,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_47])).

tff(c_51,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_51])).

tff(c_58,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_54])).

tff(c_59,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_61,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_64,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_64])).

tff(c_69,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_73,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_69])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:15:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.25  
% 1.87/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.25  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.90/1.25  
% 1.90/1.25  %Foreground sorts:
% 1.90/1.25  
% 1.90/1.25  
% 1.90/1.25  %Background operators:
% 1.90/1.25  
% 1.90/1.25  
% 1.90/1.25  %Foreground operators:
% 1.90/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.90/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.90/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.90/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.90/1.25  
% 1.90/1.26  tff(f_57, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 1.90/1.26  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.90/1.26  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_relat_1)).
% 1.90/1.26  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.90/1.26  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.90/1.26  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.90/1.26  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.90/1.26  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.90/1.26  tff(c_4, plain, (![C_5, A_3, B_4]: (r1_tarski(k7_relat_1(C_5, A_3), k7_relat_1(C_5, B_4)) | ~r1_tarski(A_3, B_4) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.90/1.26  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.26  tff(c_29, plain, (![A_20, B_21]: (r1_tarski(k2_relat_1(A_20), k2_relat_1(B_21)) | ~r1_tarski(A_20, B_21) | ~v1_relat_1(B_21) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.26  tff(c_36, plain, (![B_22, A_23, B_24]: (r1_tarski(k9_relat_1(B_22, A_23), k2_relat_1(B_24)) | ~r1_tarski(k7_relat_1(B_22, A_23), B_24) | ~v1_relat_1(B_24) | ~v1_relat_1(k7_relat_1(B_22, A_23)) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_6, c_29])).
% 1.90/1.26  tff(c_44, plain, (![B_28, A_29, B_30, A_31]: (r1_tarski(k9_relat_1(B_28, A_29), k9_relat_1(B_30, A_31)) | ~r1_tarski(k7_relat_1(B_28, A_29), k7_relat_1(B_30, A_31)) | ~v1_relat_1(k7_relat_1(B_30, A_31)) | ~v1_relat_1(k7_relat_1(B_28, A_29)) | ~v1_relat_1(B_28) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_6, c_36])).
% 1.90/1.26  tff(c_12, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.90/1.26  tff(c_47, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_12])).
% 1.90/1.26  tff(c_50, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_47])).
% 1.90/1.26  tff(c_51, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 1.90/1.26  tff(c_54, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_51])).
% 1.90/1.26  tff(c_58, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_54])).
% 1.90/1.26  tff(c_59, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 1.90/1.26  tff(c_61, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_59])).
% 1.90/1.26  tff(c_64, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_61])).
% 1.90/1.26  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_64])).
% 1.90/1.26  tff(c_69, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_59])).
% 1.90/1.26  tff(c_73, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_69])).
% 1.90/1.26  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_73])).
% 1.90/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.26  
% 1.90/1.26  Inference rules
% 1.90/1.26  ----------------------
% 1.90/1.26  #Ref     : 0
% 1.90/1.26  #Sup     : 10
% 1.90/1.26  #Fact    : 0
% 1.90/1.26  #Define  : 0
% 1.90/1.26  #Split   : 2
% 1.90/1.26  #Chain   : 0
% 1.90/1.26  #Close   : 0
% 1.90/1.26  
% 1.90/1.26  Ordering : KBO
% 1.90/1.26  
% 1.90/1.26  Simplification rules
% 1.90/1.26  ----------------------
% 1.90/1.26  #Subsume      : 1
% 1.90/1.26  #Demod        : 5
% 1.90/1.26  #Tautology    : 2
% 1.90/1.26  #SimpNegUnit  : 0
% 1.90/1.26  #BackRed      : 0
% 1.90/1.26  
% 1.90/1.26  #Partial instantiations: 0
% 1.90/1.26  #Strategies tried      : 1
% 1.90/1.26  
% 1.90/1.26  Timing (in seconds)
% 1.90/1.26  ----------------------
% 1.90/1.27  Preprocessing        : 0.25
% 1.90/1.27  Parsing              : 0.14
% 1.90/1.27  CNF conversion       : 0.02
% 1.90/1.27  Main loop            : 0.15
% 1.90/1.27  Inferencing          : 0.07
% 1.90/1.27  Reduction            : 0.03
% 1.90/1.27  Demodulation         : 0.03
% 1.90/1.27  BG Simplification    : 0.01
% 1.90/1.27  Subsumption          : 0.03
% 1.90/1.27  Abstraction          : 0.01
% 1.90/1.27  MUC search           : 0.00
% 1.90/1.27  Cooper               : 0.00
% 1.90/1.27  Total                : 0.44
% 1.90/1.27  Index Insertion      : 0.00
% 1.90/1.27  Index Deletion       : 0.00
% 1.90/1.27  Index Matching       : 0.00
% 1.90/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
