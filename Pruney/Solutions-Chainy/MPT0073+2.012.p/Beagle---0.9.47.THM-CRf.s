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
% DateTime   : Thu Dec  3 09:43:26 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   46 (  77 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 ( 128 expanded)
%              Number of equality atoms :   19 (  63 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_16,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_33,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22])).

tff(c_44,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | A_8 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_12,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_18,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_43,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_xboole_0(A_19,B_20)
      | ~ r2_hidden(C_21,k3_xboole_0(A_19,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_70,plain,(
    ! [A_22,C_23] :
      ( ~ r1_xboole_0(A_22,A_22)
      | ~ r2_hidden(C_23,A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_78,plain,(
    ! [C_24] : ~ r2_hidden(C_24,'#skF_3') ),
    inference(resolution,[status(thm)],[c_43,c_70])).

tff(c_82,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_78])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_82])).

tff(c_87,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_106,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_115,plain,(
    ! [A_31,C_32] :
      ( ~ r1_xboole_0(A_31,A_31)
      | ~ r2_hidden(C_32,A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_130,plain,(
    ! [C_34] : ~ r2_hidden(C_34,'#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_115])).

tff(c_134,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_130])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_134])).

tff(c_139,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_141,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_12])).

tff(c_140,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_146,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_140])).

tff(c_20,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_146,c_139,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:26:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.25  
% 1.74/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.26  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.74/1.26  
% 1.74/1.26  %Foreground sorts:
% 1.74/1.26  
% 1.74/1.26  
% 1.74/1.26  %Background operators:
% 1.74/1.26  
% 1.74/1.26  
% 1.74/1.26  %Foreground operators:
% 1.74/1.26  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.74/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.74/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.74/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.74/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.74/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.74/1.26  
% 1.74/1.27  tff(f_66, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.74/1.27  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.74/1.27  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.74/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.74/1.27  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.74/1.27  tff(c_16, plain, (k1_xboole_0!='#skF_3' | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.27  tff(c_22, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_16])).
% 1.74/1.27  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.74/1.27  tff(c_14, plain, (r1_xboole_0('#skF_3', '#skF_3') | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.27  tff(c_32, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_14])).
% 1.74/1.27  tff(c_33, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22])).
% 1.74/1.27  tff(c_44, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | A_8='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8])).
% 1.74/1.27  tff(c_12, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.74/1.27  tff(c_34, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 1.74/1.27  tff(c_18, plain, (r1_xboole_0('#skF_3', '#skF_3') | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.27  tff(c_43, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18])).
% 1.74/1.27  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.74/1.27  tff(c_61, plain, (![A_19, B_20, C_21]: (~r1_xboole_0(A_19, B_20) | ~r2_hidden(C_21, k3_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.74/1.27  tff(c_70, plain, (![A_22, C_23]: (~r1_xboole_0(A_22, A_22) | ~r2_hidden(C_23, A_22))), inference(superposition, [status(thm), theory('equality')], [c_2, c_61])).
% 1.74/1.27  tff(c_78, plain, (![C_24]: (~r2_hidden(C_24, '#skF_3'))), inference(resolution, [status(thm)], [c_43, c_70])).
% 1.74/1.27  tff(c_82, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_44, c_78])).
% 1.74/1.27  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_82])).
% 1.74/1.27  tff(c_87, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_14])).
% 1.74/1.27  tff(c_106, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.74/1.27  tff(c_115, plain, (![A_31, C_32]: (~r1_xboole_0(A_31, A_31) | ~r2_hidden(C_32, A_31))), inference(superposition, [status(thm), theory('equality')], [c_2, c_106])).
% 1.74/1.27  tff(c_130, plain, (![C_34]: (~r2_hidden(C_34, '#skF_3'))), inference(resolution, [status(thm)], [c_87, c_115])).
% 1.74/1.27  tff(c_134, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_130])).
% 1.74/1.27  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_134])).
% 1.74/1.27  tff(c_139, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_16])).
% 1.74/1.27  tff(c_141, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_12])).
% 1.74/1.27  tff(c_140, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_16])).
% 1.74/1.27  tff(c_146, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_140])).
% 1.74/1.27  tff(c_20, plain, (k1_xboole_0!='#skF_3' | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.27  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_146, c_139, c_20])).
% 1.74/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.27  
% 1.74/1.27  Inference rules
% 1.74/1.27  ----------------------
% 1.74/1.27  #Ref     : 0
% 1.74/1.27  #Sup     : 29
% 1.74/1.27  #Fact    : 0
% 1.74/1.27  #Define  : 0
% 1.74/1.27  #Split   : 2
% 1.74/1.27  #Chain   : 0
% 1.74/1.27  #Close   : 0
% 1.74/1.27  
% 1.74/1.27  Ordering : KBO
% 1.74/1.27  
% 1.74/1.27  Simplification rules
% 1.74/1.27  ----------------------
% 1.74/1.27  #Subsume      : 2
% 1.74/1.27  #Demod        : 12
% 1.74/1.27  #Tautology    : 16
% 1.74/1.27  #SimpNegUnit  : 2
% 1.74/1.27  #BackRed      : 3
% 1.74/1.27  
% 1.74/1.27  #Partial instantiations: 0
% 1.74/1.27  #Strategies tried      : 1
% 1.74/1.27  
% 1.74/1.27  Timing (in seconds)
% 1.74/1.27  ----------------------
% 1.74/1.27  Preprocessing        : 0.29
% 1.74/1.27  Parsing              : 0.15
% 1.74/1.27  CNF conversion       : 0.02
% 1.74/1.27  Main loop            : 0.12
% 1.74/1.27  Inferencing          : 0.05
% 1.74/1.27  Reduction            : 0.04
% 1.74/1.27  Demodulation         : 0.03
% 1.74/1.27  BG Simplification    : 0.01
% 1.74/1.27  Subsumption          : 0.01
% 1.74/1.27  Abstraction          : 0.01
% 1.74/1.27  MUC search           : 0.00
% 1.74/1.27  Cooper               : 0.00
% 1.74/1.27  Total                : 0.44
% 1.74/1.27  Index Insertion      : 0.00
% 1.74/1.27  Index Deletion       : 0.00
% 1.74/1.27  Index Matching       : 0.00
% 1.74/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
