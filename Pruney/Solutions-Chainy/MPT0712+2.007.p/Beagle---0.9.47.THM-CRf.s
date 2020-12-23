%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:32 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   42 (  62 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  91 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,k1_relat_1(B_10))
      | k11_relat_1(B_10,A_9) = k1_xboole_0
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    ! [B_26,A_27] :
      ( k1_tarski(k1_funct_1(B_26,A_27)) = k11_relat_1(B_26,A_27)
      | ~ r2_hidden(A_27,k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_90,plain,(
    ! [B_28,A_29] :
      ( k1_tarski(k1_funct_1(B_28,A_29)) = k11_relat_1(B_28,A_29)
      | ~ v1_funct_1(B_28)
      | k11_relat_1(B_28,A_29) = k1_xboole_0
      | ~ v1_relat_1(B_28) ) ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_10,plain,(
    ! [A_4,B_6] :
      ( k9_relat_1(A_4,k1_tarski(B_6)) = k11_relat_1(A_4,B_6)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_74,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_72])).

tff(c_77,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_74])).

tff(c_79,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_77])).

tff(c_96,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k11_relat_1('#skF_2','#skF_1'))
    | ~ v1_funct_1('#skF_2')
    | k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_79])).

tff(c_111,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_6,c_96])).

tff(c_118,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_79])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.25  
% 1.82/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.25  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.82/1.25  
% 1.82/1.25  %Foreground sorts:
% 1.82/1.25  
% 1.82/1.25  
% 1.82/1.25  %Background operators:
% 1.82/1.25  
% 1.82/1.25  
% 1.82/1.25  %Foreground operators:
% 1.82/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.82/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.82/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.82/1.25  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 1.82/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.82/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.82/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.82/1.25  
% 1.82/1.26  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.82/1.26  tff(f_64, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 1.82/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.82/1.26  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 1.82/1.26  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 1.82/1.26  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 1.82/1.26  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.82/1.26  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.82/1.26  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.26  tff(c_22, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.26  tff(c_14, plain, (![A_9, B_10]: (r2_hidden(A_9, k1_relat_1(B_10)) | k11_relat_1(B_10, A_9)=k1_xboole_0 | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.82/1.26  tff(c_85, plain, (![B_26, A_27]: (k1_tarski(k1_funct_1(B_26, A_27))=k11_relat_1(B_26, A_27) | ~r2_hidden(A_27, k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.26  tff(c_90, plain, (![B_28, A_29]: (k1_tarski(k1_funct_1(B_28, A_29))=k11_relat_1(B_28, A_29) | ~v1_funct_1(B_28) | k11_relat_1(B_28, A_29)=k1_xboole_0 | ~v1_relat_1(B_28))), inference(resolution, [status(thm)], [c_14, c_85])).
% 1.82/1.26  tff(c_10, plain, (![A_4, B_6]: (k9_relat_1(A_4, k1_tarski(B_6))=k11_relat_1(A_4, B_6) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.82/1.26  tff(c_12, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.82/1.26  tff(c_20, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.26  tff(c_72, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_20])).
% 1.82/1.26  tff(c_74, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_72])).
% 1.82/1.26  tff(c_77, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_74])).
% 1.82/1.26  tff(c_79, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_77])).
% 1.82/1.26  tff(c_96, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k11_relat_1('#skF_2', '#skF_1')) | ~v1_funct_1('#skF_2') | k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_79])).
% 1.82/1.26  tff(c_111, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_6, c_96])).
% 1.82/1.26  tff(c_118, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_79])).
% 1.82/1.26  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_118])).
% 1.82/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.26  
% 1.82/1.26  Inference rules
% 1.82/1.26  ----------------------
% 1.82/1.26  #Ref     : 0
% 1.82/1.26  #Sup     : 18
% 1.82/1.26  #Fact    : 0
% 1.82/1.26  #Define  : 0
% 1.82/1.26  #Split   : 1
% 1.82/1.26  #Chain   : 0
% 1.82/1.26  #Close   : 0
% 1.82/1.26  
% 1.82/1.26  Ordering : KBO
% 1.82/1.26  
% 1.82/1.26  Simplification rules
% 1.82/1.26  ----------------------
% 1.82/1.26  #Subsume      : 0
% 1.82/1.26  #Demod        : 13
% 1.82/1.26  #Tautology    : 11
% 1.82/1.26  #SimpNegUnit  : 0
% 1.82/1.26  #BackRed      : 1
% 1.82/1.26  
% 1.82/1.26  #Partial instantiations: 0
% 1.82/1.26  #Strategies tried      : 1
% 1.82/1.26  
% 1.82/1.26  Timing (in seconds)
% 1.82/1.26  ----------------------
% 1.82/1.27  Preprocessing        : 0.29
% 1.82/1.27  Parsing              : 0.16
% 1.82/1.27  CNF conversion       : 0.02
% 1.82/1.27  Main loop            : 0.13
% 1.82/1.27  Inferencing          : 0.05
% 1.82/1.27  Reduction            : 0.03
% 1.82/1.27  Demodulation         : 0.03
% 1.82/1.27  BG Simplification    : 0.01
% 1.82/1.27  Subsumption          : 0.02
% 1.82/1.27  Abstraction          : 0.01
% 1.82/1.27  MUC search           : 0.00
% 1.82/1.27  Cooper               : 0.00
% 1.82/1.27  Total                : 0.44
% 1.82/1.27  Index Insertion      : 0.00
% 1.82/1.27  Index Deletion       : 0.00
% 1.82/1.27  Index Matching       : 0.00
% 1.82/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
