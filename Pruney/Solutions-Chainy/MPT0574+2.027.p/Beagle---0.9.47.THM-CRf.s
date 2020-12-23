%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:54 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  56 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski('#skF_1'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(B_7,C_8) = A_6
      | ~ r1_tarski(A_6,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_tarski('#skF_1'(A_60,B_61,C_62),A_60)
      | k3_xboole_0(B_61,C_62) = A_60
      | ~ r1_tarski(A_60,C_62)
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_123,plain,(
    ! [B_7,C_8] :
      ( k3_xboole_0(B_7,C_8) = C_8
      | ~ r1_tarski(C_8,C_8)
      | ~ r1_tarski(C_8,B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_119])).

tff(c_127,plain,(
    ! [B_63,C_64] :
      ( k3_xboole_0(B_63,C_64) = C_64
      | ~ r1_tarski(C_64,B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_123])).

tff(c_171,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_127])).

tff(c_51,plain,(
    ! [C_21,A_22,B_23] :
      ( r1_tarski(k10_relat_1(C_21,k3_xboole_0(A_22,B_23)),k3_xboole_0(k10_relat_1(C_21,A_22),k10_relat_1(C_21,B_23)))
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k3_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [C_21,A_22,B_23] :
      ( r1_tarski(k10_relat_1(C_21,k3_xboole_0(A_22,B_23)),k10_relat_1(C_21,A_22))
      | ~ v1_relat_1(C_21) ) ),
    inference(resolution,[status(thm)],[c_51,c_8])).

tff(c_1114,plain,(
    ! [C_86] :
      ( r1_tarski(k10_relat_1(C_86,'#skF_2'),k10_relat_1(C_86,'#skF_3'))
      | ~ v1_relat_1(C_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_58])).

tff(c_18,plain,(
    ~ r1_tarski(k10_relat_1('#skF_4','#skF_2'),k10_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1125,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1114,c_18])).

tff(c_1132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.36  
% 2.55/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.36  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.55/1.36  
% 2.55/1.36  %Foreground sorts:
% 2.55/1.36  
% 2.55/1.36  
% 2.55/1.36  %Background operators:
% 2.55/1.36  
% 2.55/1.36  
% 2.55/1.36  %Foreground operators:
% 2.55/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.55/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.36  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.55/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.36  
% 2.55/1.37  tff(f_59, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 2.55/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.55/1.37  tff(f_48, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_xboole_1)).
% 2.55/1.37  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_relat_1)).
% 2.55/1.37  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.55/1.37  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.37  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.37  tff(c_12, plain, (![A_6, B_7, C_8]: (r1_tarski('#skF_1'(A_6, B_7, C_8), C_8) | k3_xboole_0(B_7, C_8)=A_6 | ~r1_tarski(A_6, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.55/1.37  tff(c_119, plain, (![A_60, B_61, C_62]: (~r1_tarski('#skF_1'(A_60, B_61, C_62), A_60) | k3_xboole_0(B_61, C_62)=A_60 | ~r1_tarski(A_60, C_62) | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.55/1.37  tff(c_123, plain, (![B_7, C_8]: (k3_xboole_0(B_7, C_8)=C_8 | ~r1_tarski(C_8, C_8) | ~r1_tarski(C_8, B_7))), inference(resolution, [status(thm)], [c_12, c_119])).
% 2.55/1.37  tff(c_127, plain, (![B_63, C_64]: (k3_xboole_0(B_63, C_64)=C_64 | ~r1_tarski(C_64, B_63))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_123])).
% 2.55/1.37  tff(c_171, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_20, c_127])).
% 2.55/1.37  tff(c_51, plain, (![C_21, A_22, B_23]: (r1_tarski(k10_relat_1(C_21, k3_xboole_0(A_22, B_23)), k3_xboole_0(k10_relat_1(C_21, A_22), k10_relat_1(C_21, B_23))) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.55/1.37  tff(c_8, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.55/1.37  tff(c_58, plain, (![C_21, A_22, B_23]: (r1_tarski(k10_relat_1(C_21, k3_xboole_0(A_22, B_23)), k10_relat_1(C_21, A_22)) | ~v1_relat_1(C_21))), inference(resolution, [status(thm)], [c_51, c_8])).
% 2.55/1.37  tff(c_1114, plain, (![C_86]: (r1_tarski(k10_relat_1(C_86, '#skF_2'), k10_relat_1(C_86, '#skF_3')) | ~v1_relat_1(C_86))), inference(superposition, [status(thm), theory('equality')], [c_171, c_58])).
% 2.55/1.37  tff(c_18, plain, (~r1_tarski(k10_relat_1('#skF_4', '#skF_2'), k10_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.37  tff(c_1125, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1114, c_18])).
% 2.55/1.37  tff(c_1132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1125])).
% 2.55/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.37  
% 2.55/1.37  Inference rules
% 2.55/1.37  ----------------------
% 2.55/1.37  #Ref     : 0
% 2.55/1.37  #Sup     : 257
% 2.55/1.37  #Fact    : 0
% 2.55/1.37  #Define  : 0
% 2.55/1.37  #Split   : 1
% 2.55/1.37  #Chain   : 0
% 2.55/1.37  #Close   : 0
% 2.55/1.37  
% 2.55/1.37  Ordering : KBO
% 2.55/1.37  
% 2.55/1.37  Simplification rules
% 2.55/1.37  ----------------------
% 2.55/1.37  #Subsume      : 16
% 2.55/1.37  #Demod        : 178
% 2.55/1.37  #Tautology    : 151
% 2.55/1.37  #SimpNegUnit  : 0
% 2.55/1.37  #BackRed      : 0
% 2.55/1.37  
% 2.55/1.37  #Partial instantiations: 0
% 2.55/1.37  #Strategies tried      : 1
% 2.55/1.37  
% 2.55/1.37  Timing (in seconds)
% 2.55/1.37  ----------------------
% 2.55/1.38  Preprocessing        : 0.26
% 2.55/1.38  Parsing              : 0.15
% 2.55/1.38  CNF conversion       : 0.02
% 2.55/1.38  Main loop            : 0.36
% 2.55/1.38  Inferencing          : 0.14
% 2.55/1.38  Reduction            : 0.11
% 2.55/1.38  Demodulation         : 0.08
% 2.55/1.38  BG Simplification    : 0.02
% 2.55/1.38  Subsumption          : 0.07
% 2.55/1.38  Abstraction          : 0.02
% 2.55/1.38  MUC search           : 0.00
% 2.55/1.38  Cooper               : 0.00
% 2.55/1.38  Total                : 0.65
% 2.55/1.38  Index Insertion      : 0.00
% 2.55/1.38  Index Deletion       : 0.00
% 2.55/1.38  Index Matching       : 0.00
% 2.55/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
