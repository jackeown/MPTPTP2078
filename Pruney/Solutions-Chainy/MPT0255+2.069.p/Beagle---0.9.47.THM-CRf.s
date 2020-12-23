%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:48 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 128 expanded)
%              Number of leaves         :   24 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 ( 145 expanded)
%              Number of equality atoms :   12 (  67 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_55,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,(
    ! [A_35,B_34] : r1_tarski(A_35,k2_xboole_0(B_34,A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_18])).

tff(c_107,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_70])).

tff(c_14,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_129,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_107,c_14])).

tff(c_116,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_235,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_116])).

tff(c_280,plain,(
    ! [A_46] :
      ( A_46 = '#skF_6'
      | ~ r1_tarski(A_46,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_129,c_14])).

tff(c_292,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_235,c_280])).

tff(c_22,plain,(
    ! [D_20,A_15] : r2_hidden(D_20,k2_tarski(A_15,D_20)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_317,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_22])).

tff(c_16,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_134,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_16])).

tff(c_528,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,B_60)
      | ~ r2_hidden(C_61,A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_532,plain,(
    ! [C_62,A_63] :
      ( ~ r2_hidden(C_62,'#skF_6')
      | ~ r2_hidden(C_62,A_63) ) ),
    inference(resolution,[status(thm)],[c_134,c_528])).

tff(c_546,plain,(
    ! [A_63] : ~ r2_hidden('#skF_5',A_63) ),
    inference(resolution,[status(thm)],[c_317,c_532])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_546,c_317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.45  
% 2.09/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.46  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.09/1.46  
% 2.09/1.46  %Foreground sorts:
% 2.09/1.46  
% 2.09/1.46  
% 2.09/1.46  %Background operators:
% 2.09/1.46  
% 2.09/1.46  
% 2.09/1.46  %Foreground operators:
% 2.09/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.09/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.09/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.46  
% 2.48/1.47  tff(f_76, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.48/1.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.48/1.47  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.48/1.47  tff(f_55, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.48/1.47  tff(f_68, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.48/1.47  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.48/1.47  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.48/1.47  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.48/1.47  tff(c_55, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.47  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.48/1.47  tff(c_70, plain, (![A_35, B_34]: (r1_tarski(A_35, k2_xboole_0(B_34, A_35)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_18])).
% 2.48/1.47  tff(c_107, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_70])).
% 2.48/1.47  tff(c_14, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.47  tff(c_129, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_107, c_14])).
% 2.48/1.47  tff(c_116, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_18])).
% 2.48/1.47  tff(c_235, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_116])).
% 2.48/1.47  tff(c_280, plain, (![A_46]: (A_46='#skF_6' | ~r1_tarski(A_46, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_129, c_14])).
% 2.48/1.47  tff(c_292, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_235, c_280])).
% 2.48/1.47  tff(c_22, plain, (![D_20, A_15]: (r2_hidden(D_20, k2_tarski(A_15, D_20)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.48/1.47  tff(c_317, plain, (r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_292, c_22])).
% 2.48/1.47  tff(c_16, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.48/1.47  tff(c_134, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_16])).
% 2.48/1.47  tff(c_528, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, B_60) | ~r2_hidden(C_61, A_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.48/1.47  tff(c_532, plain, (![C_62, A_63]: (~r2_hidden(C_62, '#skF_6') | ~r2_hidden(C_62, A_63))), inference(resolution, [status(thm)], [c_134, c_528])).
% 2.48/1.47  tff(c_546, plain, (![A_63]: (~r2_hidden('#skF_5', A_63))), inference(resolution, [status(thm)], [c_317, c_532])).
% 2.48/1.47  tff(c_549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_546, c_317])).
% 2.48/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.47  
% 2.48/1.47  Inference rules
% 2.48/1.47  ----------------------
% 2.48/1.47  #Ref     : 0
% 2.48/1.47  #Sup     : 122
% 2.48/1.47  #Fact    : 0
% 2.48/1.47  #Define  : 0
% 2.48/1.47  #Split   : 0
% 2.48/1.47  #Chain   : 0
% 2.48/1.47  #Close   : 0
% 2.48/1.47  
% 2.48/1.47  Ordering : KBO
% 2.48/1.47  
% 2.48/1.47  Simplification rules
% 2.48/1.47  ----------------------
% 2.48/1.47  #Subsume      : 0
% 2.48/1.47  #Demod        : 98
% 2.48/1.47  #Tautology    : 99
% 2.48/1.47  #SimpNegUnit  : 1
% 2.48/1.47  #BackRed      : 7
% 2.48/1.47  
% 2.48/1.47  #Partial instantiations: 0
% 2.48/1.47  #Strategies tried      : 1
% 2.48/1.47  
% 2.48/1.47  Timing (in seconds)
% 2.48/1.47  ----------------------
% 2.48/1.47  Preprocessing        : 0.41
% 2.48/1.47  Parsing              : 0.24
% 2.48/1.47  CNF conversion       : 0.02
% 2.48/1.47  Main loop            : 0.24
% 2.48/1.47  Inferencing          : 0.08
% 2.48/1.47  Reduction            : 0.09
% 2.48/1.47  Demodulation         : 0.07
% 2.48/1.47  BG Simplification    : 0.01
% 2.48/1.47  Subsumption          : 0.04
% 2.48/1.47  Abstraction          : 0.02
% 2.48/1.47  MUC search           : 0.00
% 2.48/1.47  Cooper               : 0.00
% 2.48/1.47  Total                : 0.67
% 2.48/1.47  Index Insertion      : 0.00
% 2.48/1.47  Index Deletion       : 0.00
% 2.48/1.47  Index Matching       : 0.00
% 2.48/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
