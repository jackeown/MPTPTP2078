%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:30 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   47 (  67 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  87 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_189,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_xboole_0(A_40,C_41)
      | ~ r1_xboole_0(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_195,plain,(
    ! [A_40] :
      ( r1_xboole_0(A_40,'#skF_4')
      | ~ r1_tarski(A_40,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_189])).

tff(c_14,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_59,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_71,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_16])).

tff(c_90,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_108,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_90])).

tff(c_118,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_108])).

tff(c_145,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_151,plain,(
    ! [C_38] :
      ( ~ r1_xboole_0('#skF_5','#skF_4')
      | ~ r2_hidden(C_38,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_145])).

tff(c_259,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_276,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_195,c_259])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_276])).

tff(c_286,plain,(
    ! [C_53] : ~ r2_hidden(C_53,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_290,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_286])).

tff(c_294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.27  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.06/1.27  
% 2.06/1.27  %Foreground sorts:
% 2.06/1.27  
% 2.06/1.27  
% 2.06/1.27  %Background operators:
% 2.06/1.27  
% 2.06/1.27  
% 2.06/1.27  %Foreground operators:
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.27  
% 2.06/1.28  tff(f_76, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.06/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.06/1.28  tff(f_65, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.06/1.28  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.06/1.28  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.06/1.28  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.06/1.28  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.06/1.28  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.06/1.28  tff(c_28, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.06/1.28  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.28  tff(c_26, plain, (r1_tarski('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.06/1.28  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.06/1.28  tff(c_189, plain, (![A_40, C_41, B_42]: (r1_xboole_0(A_40, C_41) | ~r1_xboole_0(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.06/1.28  tff(c_195, plain, (![A_40]: (r1_xboole_0(A_40, '#skF_4') | ~r1_tarski(A_40, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_189])).
% 2.06/1.28  tff(c_14, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.28  tff(c_24, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.06/1.28  tff(c_59, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.06/1.28  tff(c_66, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_24, c_59])).
% 2.06/1.28  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.06/1.28  tff(c_71, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_66, c_16])).
% 2.06/1.28  tff(c_90, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.06/1.28  tff(c_108, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_71, c_90])).
% 2.06/1.28  tff(c_118, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_108])).
% 2.06/1.28  tff(c_145, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.28  tff(c_151, plain, (![C_38]: (~r1_xboole_0('#skF_5', '#skF_4') | ~r2_hidden(C_38, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_145])).
% 2.06/1.28  tff(c_259, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_151])).
% 2.06/1.28  tff(c_276, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_195, c_259])).
% 2.06/1.28  tff(c_283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_276])).
% 2.06/1.28  tff(c_286, plain, (![C_53]: (~r2_hidden(C_53, '#skF_5'))), inference(splitRight, [status(thm)], [c_151])).
% 2.06/1.28  tff(c_290, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_286])).
% 2.06/1.28  tff(c_294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_290])).
% 2.06/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.28  
% 2.06/1.28  Inference rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Ref     : 0
% 2.06/1.28  #Sup     : 72
% 2.06/1.28  #Fact    : 0
% 2.06/1.28  #Define  : 0
% 2.06/1.28  #Split   : 4
% 2.06/1.28  #Chain   : 0
% 2.06/1.28  #Close   : 0
% 2.06/1.28  
% 2.06/1.28  Ordering : KBO
% 2.06/1.28  
% 2.06/1.28  Simplification rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Subsume      : 3
% 2.06/1.28  #Demod        : 9
% 2.06/1.28  #Tautology    : 30
% 2.06/1.28  #SimpNegUnit  : 2
% 2.06/1.28  #BackRed      : 0
% 2.06/1.28  
% 2.06/1.28  #Partial instantiations: 0
% 2.06/1.28  #Strategies tried      : 1
% 2.06/1.28  
% 2.06/1.28  Timing (in seconds)
% 2.06/1.28  ----------------------
% 2.06/1.28  Preprocessing        : 0.28
% 2.06/1.28  Parsing              : 0.16
% 2.06/1.28  CNF conversion       : 0.02
% 2.06/1.29  Main loop            : 0.23
% 2.06/1.29  Inferencing          : 0.10
% 2.06/1.29  Reduction            : 0.06
% 2.06/1.29  Demodulation         : 0.04
% 2.06/1.29  BG Simplification    : 0.01
% 2.06/1.29  Subsumption          : 0.04
% 2.06/1.29  Abstraction          : 0.01
% 2.06/1.29  MUC search           : 0.00
% 2.06/1.29  Cooper               : 0.00
% 2.06/1.29  Total                : 0.55
% 2.06/1.29  Index Insertion      : 0.00
% 2.06/1.29  Index Deletion       : 0.00
% 2.06/1.29  Index Matching       : 0.00
% 2.06/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
