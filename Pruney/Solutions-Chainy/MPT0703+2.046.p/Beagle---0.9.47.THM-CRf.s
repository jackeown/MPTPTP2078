%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:14 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   39 (  49 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   56 (  94 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_12,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k9_relat_1(B_10,k10_relat_1(B_10,A_9)),A_9)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69,plain,(
    ! [B_27,A_28] :
      ( k9_relat_1(B_27,k10_relat_1(B_27,A_28)) = A_28
      | ~ r1_tarski(A_28,k2_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_74,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_78,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_74])).

tff(c_6,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k9_relat_1(C_8,A_6),k9_relat_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [B_7] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_7))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_7)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_6])).

tff(c_115,plain,(
    ! [B_29] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_29))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_85])).

tff(c_119,plain,(
    r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16,c_115])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    k2_xboole_0('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2'))) = k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_119,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_146,plain,(
    ! [C_32] :
      ( r1_tarski('#skF_1',C_32)
      | ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')),C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_2])).

tff(c_158,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_146])).

tff(c_166,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_158])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n014.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 10:09:52 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.06  
% 1.78/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.06  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.78/1.06  
% 1.78/1.06  %Foreground sorts:
% 1.78/1.06  
% 1.78/1.06  
% 1.78/1.06  %Background operators:
% 1.78/1.06  
% 1.78/1.06  
% 1.78/1.06  %Foreground operators:
% 1.78/1.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.78/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.78/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.06  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.78/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.06  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.78/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.06  
% 1.78/1.07  tff(f_64, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 1.78/1.07  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 1.78/1.07  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 1.78/1.07  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 1.78/1.07  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.78/1.07  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.78/1.07  tff(c_12, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.78/1.07  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.78/1.07  tff(c_18, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.78/1.07  tff(c_8, plain, (![B_10, A_9]: (r1_tarski(k9_relat_1(B_10, k10_relat_1(B_10, A_9)), A_9) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.07  tff(c_16, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.78/1.07  tff(c_14, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.78/1.07  tff(c_69, plain, (![B_27, A_28]: (k9_relat_1(B_27, k10_relat_1(B_27, A_28))=A_28 | ~r1_tarski(A_28, k2_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.78/1.07  tff(c_74, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_69])).
% 1.78/1.07  tff(c_78, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_74])).
% 1.78/1.07  tff(c_6, plain, (![C_8, A_6, B_7]: (r1_tarski(k9_relat_1(C_8, A_6), k9_relat_1(C_8, B_7)) | ~r1_tarski(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.78/1.07  tff(c_85, plain, (![B_7]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_7)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_7) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_6])).
% 1.78/1.07  tff(c_115, plain, (![B_29]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_29)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_29))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_85])).
% 1.78/1.07  tff(c_119, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_16, c_115])).
% 1.78/1.07  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.07  tff(c_123, plain, (k2_xboole_0('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')))=k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_119, c_4])).
% 1.78/1.07  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.07  tff(c_146, plain, (![C_32]: (r1_tarski('#skF_1', C_32) | ~r1_tarski(k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')), C_32))), inference(superposition, [status(thm), theory('equality')], [c_123, c_2])).
% 1.78/1.07  tff(c_158, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_146])).
% 1.78/1.07  tff(c_166, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_158])).
% 1.78/1.07  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_166])).
% 1.78/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.07  
% 1.78/1.07  Inference rules
% 1.78/1.07  ----------------------
% 1.78/1.07  #Ref     : 0
% 1.78/1.07  #Sup     : 36
% 1.78/1.07  #Fact    : 0
% 1.78/1.07  #Define  : 0
% 1.78/1.07  #Split   : 0
% 1.78/1.07  #Chain   : 0
% 1.78/1.07  #Close   : 0
% 1.78/1.07  
% 1.78/1.07  Ordering : KBO
% 1.78/1.07  
% 1.78/1.07  Simplification rules
% 1.78/1.07  ----------------------
% 1.78/1.07  #Subsume      : 0
% 1.78/1.07  #Demod        : 14
% 1.78/1.07  #Tautology    : 16
% 1.78/1.07  #SimpNegUnit  : 1
% 1.78/1.07  #BackRed      : 0
% 1.78/1.07  
% 1.78/1.07  #Partial instantiations: 0
% 1.78/1.07  #Strategies tried      : 1
% 1.78/1.07  
% 1.78/1.07  Timing (in seconds)
% 1.78/1.07  ----------------------
% 1.78/1.07  Preprocessing        : 0.26
% 1.78/1.07  Parsing              : 0.15
% 1.78/1.07  CNF conversion       : 0.02
% 1.78/1.07  Main loop            : 0.16
% 1.78/1.07  Inferencing          : 0.07
% 1.78/1.07  Reduction            : 0.04
% 1.78/1.07  Demodulation         : 0.03
% 1.78/1.07  BG Simplification    : 0.01
% 1.78/1.07  Subsumption          : 0.03
% 1.78/1.07  Abstraction          : 0.01
% 1.78/1.07  MUC search           : 0.00
% 1.78/1.07  Cooper               : 0.00
% 1.78/1.07  Total                : 0.44
% 1.78/1.07  Index Insertion      : 0.00
% 1.78/1.07  Index Deletion       : 0.00
% 1.78/1.07  Index Matching       : 0.00
% 1.78/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
