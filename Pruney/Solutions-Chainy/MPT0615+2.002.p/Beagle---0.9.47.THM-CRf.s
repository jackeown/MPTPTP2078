%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:48 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   40 (  55 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 ( 101 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_93,plain,(
    r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_18,plain,
    ( ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_147,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_18])).

tff(c_10,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k7_relat_1(B_13,A_12),B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    k3_xboole_0('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_93,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_tarski(k3_xboole_0(A_25,C_26),B_27)
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [B_28,A_29,B_30] :
      ( r1_tarski(k3_xboole_0(B_28,A_29),B_30)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_148,plain,(
    ! [B_31] :
      ( r1_tarski('#skF_1',B_31)
      | ~ r1_tarski(k7_relat_1('#skF_2',k1_relat_1('#skF_1')),B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_126])).

tff(c_156,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_148])).

tff(c_161,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_156])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_161])).

tff(c_164,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_12,plain,(
    ! [A_14] :
      ( k7_relat_1(A_14,k1_relat_1(A_14)) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_220,plain,(
    ! [B_38,A_39,C_40] :
      ( r1_tarski(k7_relat_1(B_38,A_39),k7_relat_1(C_40,A_39))
      | ~ r1_tarski(B_38,C_40)
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_658,plain,(
    ! [A_67,C_68] :
      ( r1_tarski(A_67,k7_relat_1(C_68,k1_relat_1(A_67)))
      | ~ r1_tarski(A_67,C_68)
      | ~ v1_relat_1(C_68)
      | ~ v1_relat_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_220])).

tff(c_171,plain,(
    ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_18])).

tff(c_683,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_658,c_171])).

tff(c_712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_164,c_683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:15:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.48  
% 2.69/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.48  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.69/1.48  
% 2.69/1.48  %Foreground sorts:
% 2.69/1.48  
% 2.69/1.48  
% 2.69/1.48  %Background operators:
% 2.69/1.48  
% 2.69/1.48  
% 2.69/1.48  %Foreground operators:
% 2.69/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.69/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.48  
% 2.80/1.49  tff(f_62, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t219_relat_1)).
% 2.80/1.49  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.80/1.49  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.80/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.80/1.49  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.80/1.49  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.80/1.49  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 2.80/1.49  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.80/1.49  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.80/1.49  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2') | r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.80/1.49  tff(c_93, plain, (r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_24])).
% 2.80/1.49  tff(c_18, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1'))) | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.80/1.49  tff(c_147, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_18])).
% 2.80/1.49  tff(c_10, plain, (![B_13, A_12]: (r1_tarski(k7_relat_1(B_13, A_12), B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.49  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.49  tff(c_101, plain, (k3_xboole_0('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))='#skF_1'), inference(resolution, [status(thm)], [c_93, c_6])).
% 2.80/1.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.80/1.49  tff(c_106, plain, (![A_25, C_26, B_27]: (r1_tarski(k3_xboole_0(A_25, C_26), B_27) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.49  tff(c_126, plain, (![B_28, A_29, B_30]: (r1_tarski(k3_xboole_0(B_28, A_29), B_30) | ~r1_tarski(A_29, B_30))), inference(superposition, [status(thm), theory('equality')], [c_2, c_106])).
% 2.80/1.49  tff(c_148, plain, (![B_31]: (r1_tarski('#skF_1', B_31) | ~r1_tarski(k7_relat_1('#skF_2', k1_relat_1('#skF_1')), B_31))), inference(superposition, [status(thm), theory('equality')], [c_101, c_126])).
% 2.80/1.49  tff(c_156, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_148])).
% 2.80/1.49  tff(c_161, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_156])).
% 2.80/1.49  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_161])).
% 2.80/1.49  tff(c_164, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_24])).
% 2.80/1.49  tff(c_12, plain, (![A_14]: (k7_relat_1(A_14, k1_relat_1(A_14))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.80/1.49  tff(c_220, plain, (![B_38, A_39, C_40]: (r1_tarski(k7_relat_1(B_38, A_39), k7_relat_1(C_40, A_39)) | ~r1_tarski(B_38, C_40) | ~v1_relat_1(C_40) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.80/1.49  tff(c_658, plain, (![A_67, C_68]: (r1_tarski(A_67, k7_relat_1(C_68, k1_relat_1(A_67))) | ~r1_tarski(A_67, C_68) | ~v1_relat_1(C_68) | ~v1_relat_1(A_67) | ~v1_relat_1(A_67))), inference(superposition, [status(thm), theory('equality')], [c_12, c_220])).
% 2.80/1.49  tff(c_171, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_18])).
% 2.80/1.49  tff(c_683, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_658, c_171])).
% 2.80/1.49  tff(c_712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_164, c_683])).
% 2.80/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.49  
% 2.80/1.49  Inference rules
% 2.80/1.49  ----------------------
% 2.80/1.49  #Ref     : 0
% 2.80/1.49  #Sup     : 182
% 2.80/1.49  #Fact    : 0
% 2.80/1.49  #Define  : 0
% 2.80/1.49  #Split   : 2
% 2.80/1.49  #Chain   : 0
% 2.80/1.49  #Close   : 0
% 2.80/1.49  
% 2.80/1.49  Ordering : KBO
% 2.80/1.49  
% 2.80/1.49  Simplification rules
% 2.80/1.49  ----------------------
% 2.80/1.49  #Subsume      : 28
% 2.80/1.49  #Demod        : 50
% 2.80/1.49  #Tautology    : 63
% 2.80/1.49  #SimpNegUnit  : 1
% 2.80/1.49  #BackRed      : 0
% 2.80/1.49  
% 2.80/1.49  #Partial instantiations: 0
% 2.80/1.49  #Strategies tried      : 1
% 2.80/1.49  
% 2.80/1.49  Timing (in seconds)
% 2.80/1.49  ----------------------
% 2.80/1.49  Preprocessing        : 0.31
% 2.80/1.49  Parsing              : 0.16
% 2.80/1.49  CNF conversion       : 0.02
% 2.80/1.49  Main loop            : 0.35
% 2.80/1.49  Inferencing          : 0.13
% 2.80/1.49  Reduction            : 0.11
% 2.80/1.49  Demodulation         : 0.08
% 2.80/1.49  BG Simplification    : 0.02
% 2.80/1.49  Subsumption          : 0.07
% 2.80/1.49  Abstraction          : 0.02
% 2.80/1.49  MUC search           : 0.00
% 2.80/1.49  Cooper               : 0.00
% 2.80/1.49  Total                : 0.69
% 2.80/1.49  Index Insertion      : 0.00
% 2.80/1.49  Index Deletion       : 0.00
% 2.80/1.49  Index Matching       : 0.00
% 2.80/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
