%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:54 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   68 ( 109 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v2_funct_1(A)
              & r1_tarski(B,k1_relat_1(A)) )
           => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    ! [B_14,A_15] :
      ( k9_relat_1(k2_funct_1(B_14),A_15) = k10_relat_1(B_14,A_15)
      | ~ v2_funct_1(B_14)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),k9_relat_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,
    ( k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) != '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_14])).

tff(c_48,plain,(
    k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_42])).

tff(c_16,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_18,C_19,B_20] :
      ( r1_tarski(A_18,k10_relat_1(C_19,B_20))
      | ~ r1_tarski(k9_relat_1(C_19,A_18),B_20)
      | ~ r1_tarski(A_18,k1_relat_1(C_19))
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    ! [A_18,C_19] :
      ( r1_tarski(A_18,k10_relat_1(C_19,k9_relat_1(C_19,A_18)))
      | ~ r1_tarski(A_18,k1_relat_1(C_19))
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_50,plain,(
    ! [B_16,A_17] :
      ( r1_tarski(k10_relat_1(B_16,k9_relat_1(B_16,A_17)),A_17)
      | ~ v2_funct_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [B_23,A_24] :
      ( k10_relat_1(B_23,k9_relat_1(B_23,A_24)) = A_24
      | ~ r1_tarski(A_24,k10_relat_1(B_23,k9_relat_1(B_23,A_24)))
      | ~ v2_funct_1(B_23)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_90,plain,(
    ! [C_27,A_28] :
      ( k10_relat_1(C_27,k9_relat_1(C_27,A_28)) = A_28
      | ~ v2_funct_1(C_27)
      | ~ r1_tarski(A_28,k1_relat_1(C_27))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(resolution,[status(thm)],[c_65,c_78])).

tff(c_98,plain,
    ( k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_90])).

tff(c_106,plain,(
    k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_98])).

tff(c_108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.28  
% 1.93/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.28  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.93/1.28  
% 1.93/1.28  %Foreground sorts:
% 1.93/1.28  
% 1.93/1.28  
% 1.93/1.28  %Background operators:
% 1.93/1.28  
% 1.93/1.28  
% 1.93/1.28  %Foreground operators:
% 1.93/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.28  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.93/1.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.93/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.93/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.93/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.28  
% 1.93/1.29  tff(f_69, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 1.93/1.29  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 1.93/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.93/1.29  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 1.93/1.29  tff(f_39, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 1.93/1.29  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.29  tff(c_20, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.29  tff(c_18, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.29  tff(c_36, plain, (![B_14, A_15]: (k9_relat_1(k2_funct_1(B_14), A_15)=k10_relat_1(B_14, A_15) | ~v2_funct_1(B_14) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.29  tff(c_14, plain, (k9_relat_1(k2_funct_1('#skF_1'), k9_relat_1('#skF_1', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.29  tff(c_42, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))!='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_14])).
% 1.93/1.29  tff(c_48, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_42])).
% 1.93/1.29  tff(c_16, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.29  tff(c_57, plain, (![A_18, C_19, B_20]: (r1_tarski(A_18, k10_relat_1(C_19, B_20)) | ~r1_tarski(k9_relat_1(C_19, A_18), B_20) | ~r1_tarski(A_18, k1_relat_1(C_19)) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.29  tff(c_65, plain, (![A_18, C_19]: (r1_tarski(A_18, k10_relat_1(C_19, k9_relat_1(C_19, A_18))) | ~r1_tarski(A_18, k1_relat_1(C_19)) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(resolution, [status(thm)], [c_6, c_57])).
% 1.93/1.29  tff(c_50, plain, (![B_16, A_17]: (r1_tarski(k10_relat_1(B_16, k9_relat_1(B_16, A_17)), A_17) | ~v2_funct_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.29  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.29  tff(c_78, plain, (![B_23, A_24]: (k10_relat_1(B_23, k9_relat_1(B_23, A_24))=A_24 | ~r1_tarski(A_24, k10_relat_1(B_23, k9_relat_1(B_23, A_24))) | ~v2_funct_1(B_23) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(resolution, [status(thm)], [c_50, c_2])).
% 1.93/1.29  tff(c_90, plain, (![C_27, A_28]: (k10_relat_1(C_27, k9_relat_1(C_27, A_28))=A_28 | ~v2_funct_1(C_27) | ~r1_tarski(A_28, k1_relat_1(C_27)) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(resolution, [status(thm)], [c_65, c_78])).
% 1.93/1.29  tff(c_98, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_90])).
% 1.93/1.29  tff(c_106, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_98])).
% 1.93/1.29  tff(c_108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_106])).
% 1.93/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.29  
% 1.93/1.29  Inference rules
% 1.93/1.29  ----------------------
% 1.93/1.29  #Ref     : 0
% 1.93/1.29  #Sup     : 19
% 1.93/1.29  #Fact    : 0
% 1.93/1.29  #Define  : 0
% 1.93/1.29  #Split   : 1
% 1.93/1.29  #Chain   : 0
% 1.93/1.29  #Close   : 0
% 1.93/1.29  
% 1.93/1.29  Ordering : KBO
% 1.93/1.29  
% 1.93/1.29  Simplification rules
% 1.93/1.29  ----------------------
% 1.93/1.29  #Subsume      : 0
% 1.93/1.29  #Demod        : 8
% 1.93/1.29  #Tautology    : 4
% 1.93/1.29  #SimpNegUnit  : 1
% 1.93/1.29  #BackRed      : 0
% 1.93/1.29  
% 1.93/1.29  #Partial instantiations: 0
% 1.93/1.29  #Strategies tried      : 1
% 1.93/1.29  
% 1.93/1.29  Timing (in seconds)
% 1.93/1.29  ----------------------
% 1.93/1.29  Preprocessing        : 0.29
% 1.93/1.29  Parsing              : 0.16
% 1.93/1.30  CNF conversion       : 0.02
% 1.93/1.30  Main loop            : 0.20
% 1.93/1.30  Inferencing          : 0.08
% 1.93/1.30  Reduction            : 0.05
% 1.93/1.30  Demodulation         : 0.04
% 1.93/1.30  BG Simplification    : 0.01
% 1.93/1.30  Subsumption          : 0.05
% 1.93/1.30  Abstraction          : 0.01
% 1.93/1.30  MUC search           : 0.00
% 1.93/1.30  Cooper               : 0.00
% 1.93/1.30  Total                : 0.51
% 1.93/1.30  Index Insertion      : 0.00
% 1.93/1.30  Index Deletion       : 0.00
% 1.93/1.30  Index Matching       : 0.00
% 1.93/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
