%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:53 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  54 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [C_34,A_35,B_36] :
      ( r1_tarski(C_34,'#skF_1'(A_35,B_36,C_34))
      | k2_xboole_0(A_35,C_34) = B_36
      | ~ r1_tarski(C_34,B_36)
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [B_4,A_3,C_5] :
      ( ~ r1_tarski(B_4,'#skF_1'(A_3,B_4,C_5))
      | k2_xboole_0(A_3,C_5) = B_4
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_135,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(B_36,B_36)
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_128,c_8])).

tff(c_160,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_135])).

tff(c_185,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_160])).

tff(c_41,plain,(
    ! [C_19,A_20,B_21] :
      ( k2_xboole_0(k10_relat_1(C_19,A_20),k10_relat_1(C_19,B_21)) = k10_relat_1(C_19,k2_xboole_0(A_20,B_21))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ! [C_19,A_20,B_21] :
      ( r1_tarski(k10_relat_1(C_19,A_20),k10_relat_1(C_19,k2_xboole_0(A_20,B_21)))
      | ~ v1_relat_1(C_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_14])).

tff(c_201,plain,(
    ! [C_39] :
      ( r1_tarski(k10_relat_1(C_39,'#skF_2'),k10_relat_1(C_39,'#skF_3'))
      | ~ v1_relat_1(C_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_50])).

tff(c_18,plain,(
    ~ r1_tarski(k10_relat_1('#skF_4','#skF_2'),k10_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_212,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_201,c_18])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:43:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.18  
% 1.85/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.18  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.85/1.18  
% 1.85/1.18  %Foreground sorts:
% 1.85/1.18  
% 1.85/1.18  
% 1.85/1.18  %Background operators:
% 1.85/1.18  
% 1.85/1.18  
% 1.85/1.18  %Foreground operators:
% 1.85/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.85/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.85/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.18  
% 1.85/1.19  tff(f_57, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 1.85/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.85/1.19  tff(f_44, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 1.85/1.19  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 1.85/1.19  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.85/1.19  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.85/1.19  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.85/1.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.19  tff(c_128, plain, (![C_34, A_35, B_36]: (r1_tarski(C_34, '#skF_1'(A_35, B_36, C_34)) | k2_xboole_0(A_35, C_34)=B_36 | ~r1_tarski(C_34, B_36) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.19  tff(c_8, plain, (![B_4, A_3, C_5]: (~r1_tarski(B_4, '#skF_1'(A_3, B_4, C_5)) | k2_xboole_0(A_3, C_5)=B_4 | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.19  tff(c_135, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(B_36, B_36) | ~r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_128, c_8])).
% 1.85/1.19  tff(c_160, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_135])).
% 1.85/1.19  tff(c_185, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_20, c_160])).
% 1.85/1.19  tff(c_41, plain, (![C_19, A_20, B_21]: (k2_xboole_0(k10_relat_1(C_19, A_20), k10_relat_1(C_19, B_21))=k10_relat_1(C_19, k2_xboole_0(A_20, B_21)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.85/1.19  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.85/1.19  tff(c_50, plain, (![C_19, A_20, B_21]: (r1_tarski(k10_relat_1(C_19, A_20), k10_relat_1(C_19, k2_xboole_0(A_20, B_21))) | ~v1_relat_1(C_19))), inference(superposition, [status(thm), theory('equality')], [c_41, c_14])).
% 1.85/1.19  tff(c_201, plain, (![C_39]: (r1_tarski(k10_relat_1(C_39, '#skF_2'), k10_relat_1(C_39, '#skF_3')) | ~v1_relat_1(C_39))), inference(superposition, [status(thm), theory('equality')], [c_185, c_50])).
% 1.85/1.19  tff(c_18, plain, (~r1_tarski(k10_relat_1('#skF_4', '#skF_2'), k10_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.85/1.19  tff(c_212, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_201, c_18])).
% 1.85/1.19  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_212])).
% 1.85/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  Inference rules
% 1.85/1.19  ----------------------
% 1.85/1.19  #Ref     : 0
% 1.85/1.19  #Sup     : 46
% 1.85/1.19  #Fact    : 0
% 1.85/1.19  #Define  : 0
% 1.85/1.19  #Split   : 1
% 1.85/1.19  #Chain   : 0
% 1.85/1.19  #Close   : 0
% 1.85/1.19  
% 1.85/1.19  Ordering : KBO
% 1.85/1.19  
% 1.85/1.19  Simplification rules
% 1.85/1.19  ----------------------
% 1.85/1.19  #Subsume      : 1
% 1.85/1.19  #Demod        : 18
% 1.85/1.19  #Tautology    : 20
% 1.85/1.19  #SimpNegUnit  : 0
% 1.85/1.19  #BackRed      : 0
% 1.85/1.19  
% 1.85/1.19  #Partial instantiations: 0
% 1.85/1.19  #Strategies tried      : 1
% 1.85/1.19  
% 1.85/1.19  Timing (in seconds)
% 1.85/1.19  ----------------------
% 1.85/1.20  Preprocessing        : 0.26
% 1.85/1.20  Parsing              : 0.15
% 1.85/1.20  CNF conversion       : 0.02
% 1.85/1.20  Main loop            : 0.18
% 1.85/1.20  Inferencing          : 0.07
% 1.85/1.20  Reduction            : 0.05
% 1.85/1.20  Demodulation         : 0.04
% 1.85/1.20  BG Simplification    : 0.01
% 1.85/1.20  Subsumption          : 0.04
% 1.85/1.20  Abstraction          : 0.01
% 1.85/1.20  MUC search           : 0.00
% 1.85/1.20  Cooper               : 0.00
% 1.85/1.20  Total                : 0.47
% 1.85/1.20  Index Insertion      : 0.00
% 1.85/1.20  Index Deletion       : 0.00
% 1.85/1.20  Index Matching       : 0.00
% 1.85/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
