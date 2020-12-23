%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:52 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :   40 (  96 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 ( 203 expanded)
%              Number of equality atoms :   22 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_434,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden('#skF_3'(A_82,B_83,C_84),A_82)
      | r2_hidden('#skF_4'(A_82,B_83,C_84),C_84)
      | k4_xboole_0(A_82,B_83) = C_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [A_7,B_8,C_9] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8,C_9),B_8)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_520,plain,(
    ! [A_82,C_84] :
      ( r2_hidden('#skF_4'(A_82,A_82,C_84),C_84)
      | k4_xboole_0(A_82,A_82) = C_84 ) ),
    inference(resolution,[status(thm)],[c_434,c_34])).

tff(c_544,plain,(
    ! [A_85,C_86] :
      ( r2_hidden('#skF_4'(A_85,A_85,C_86),C_86)
      | k4_xboole_0(A_85,A_85) = C_86 ) ),
    inference(resolution,[status(thm)],[c_434,c_34])).

tff(c_40,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_76,plain,(
    ! [D_31,B_32,A_33] :
      ( ~ r2_hidden(D_31,B_32)
      | ~ r2_hidden(D_31,k4_xboole_0(A_33,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_79,plain,(
    ! [D_31,A_14] :
      ( ~ r2_hidden(D_31,k1_xboole_0)
      | ~ r2_hidden(D_31,A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_76])).

tff(c_597,plain,(
    ! [A_87,A_88] :
      ( ~ r2_hidden('#skF_4'(A_87,A_87,k1_xboole_0),A_88)
      | k4_xboole_0(A_87,A_87) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_544,c_79])).

tff(c_618,plain,(
    ! [A_82] : k4_xboole_0(A_82,A_82) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_520,c_597])).

tff(c_790,plain,(
    ! [A_94,C_95] :
      ( r2_hidden('#skF_4'(A_94,A_94,C_95),C_95)
      | k1_xboole_0 = C_95 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_520])).

tff(c_24,plain,(
    ! [D_12,A_7,B_8] :
      ( r2_hidden(D_12,A_7)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3357,plain,(
    ! [A_163,A_164,B_165] :
      ( r2_hidden('#skF_4'(A_163,A_163,k4_xboole_0(A_164,B_165)),A_164)
      | k4_xboole_0(A_164,B_165) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_790,c_24])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3240,plain,(
    ! [A_158,A_159,B_160] :
      ( ~ r2_hidden('#skF_4'(A_158,A_158,k4_xboole_0(A_159,B_160)),B_160)
      | k4_xboole_0(A_159,B_160) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_790,c_22])).

tff(c_3312,plain,(
    ! [A_158,A_14] :
      ( ~ r2_hidden('#skF_4'(A_158,A_158,A_14),k1_xboole_0)
      | k4_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3240])).

tff(c_3335,plain,(
    ! [A_158,A_14] :
      ( ~ r2_hidden('#skF_4'(A_158,A_158,A_14),k1_xboole_0)
      | k1_xboole_0 = A_14 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3312])).

tff(c_3486,plain,(
    ! [B_165] : k4_xboole_0(k1_xboole_0,B_165) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3357,c_3335])).

tff(c_625,plain,(
    ! [A_89] : k4_xboole_0(A_89,A_89) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_520,c_597])).

tff(c_42,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k4_xboole_0(A_15,B_16),C_17) = k4_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_661,plain,(
    ! [A_89,C_17] : k4_xboole_0(A_89,k2_xboole_0(A_89,C_17)) = k4_xboole_0(k1_xboole_0,C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_42])).

tff(c_44,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_845,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_44])).

tff(c_3750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3486,c_845])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.78  
% 4.62/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.79  %$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 4.63/1.79  
% 4.63/1.79  %Foreground sorts:
% 4.63/1.79  
% 4.63/1.79  
% 4.63/1.79  %Background operators:
% 4.63/1.79  
% 4.63/1.79  
% 4.63/1.79  %Foreground operators:
% 4.63/1.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.63/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.63/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.63/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.79  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.63/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.63/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.63/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.79  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.63/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.63/1.79  
% 4.63/1.80  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.63/1.80  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.63/1.80  tff(f_50, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.63/1.80  tff(f_53, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.63/1.80  tff(c_434, plain, (![A_82, B_83, C_84]: (r2_hidden('#skF_3'(A_82, B_83, C_84), A_82) | r2_hidden('#skF_4'(A_82, B_83, C_84), C_84) | k4_xboole_0(A_82, B_83)=C_84)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.63/1.80  tff(c_34, plain, (![A_7, B_8, C_9]: (~r2_hidden('#skF_3'(A_7, B_8, C_9), B_8) | r2_hidden('#skF_4'(A_7, B_8, C_9), C_9) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.63/1.80  tff(c_520, plain, (![A_82, C_84]: (r2_hidden('#skF_4'(A_82, A_82, C_84), C_84) | k4_xboole_0(A_82, A_82)=C_84)), inference(resolution, [status(thm)], [c_434, c_34])).
% 4.63/1.80  tff(c_544, plain, (![A_85, C_86]: (r2_hidden('#skF_4'(A_85, A_85, C_86), C_86) | k4_xboole_0(A_85, A_85)=C_86)), inference(resolution, [status(thm)], [c_434, c_34])).
% 4.63/1.80  tff(c_40, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.63/1.80  tff(c_76, plain, (![D_31, B_32, A_33]: (~r2_hidden(D_31, B_32) | ~r2_hidden(D_31, k4_xboole_0(A_33, B_32)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.63/1.80  tff(c_79, plain, (![D_31, A_14]: (~r2_hidden(D_31, k1_xboole_0) | ~r2_hidden(D_31, A_14))), inference(superposition, [status(thm), theory('equality')], [c_40, c_76])).
% 4.63/1.80  tff(c_597, plain, (![A_87, A_88]: (~r2_hidden('#skF_4'(A_87, A_87, k1_xboole_0), A_88) | k4_xboole_0(A_87, A_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_544, c_79])).
% 4.63/1.80  tff(c_618, plain, (![A_82]: (k4_xboole_0(A_82, A_82)=k1_xboole_0)), inference(resolution, [status(thm)], [c_520, c_597])).
% 4.63/1.80  tff(c_790, plain, (![A_94, C_95]: (r2_hidden('#skF_4'(A_94, A_94, C_95), C_95) | k1_xboole_0=C_95)), inference(demodulation, [status(thm), theory('equality')], [c_618, c_520])).
% 4.63/1.80  tff(c_24, plain, (![D_12, A_7, B_8]: (r2_hidden(D_12, A_7) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.63/1.80  tff(c_3357, plain, (![A_163, A_164, B_165]: (r2_hidden('#skF_4'(A_163, A_163, k4_xboole_0(A_164, B_165)), A_164) | k4_xboole_0(A_164, B_165)=k1_xboole_0)), inference(resolution, [status(thm)], [c_790, c_24])).
% 4.63/1.80  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.63/1.80  tff(c_3240, plain, (![A_158, A_159, B_160]: (~r2_hidden('#skF_4'(A_158, A_158, k4_xboole_0(A_159, B_160)), B_160) | k4_xboole_0(A_159, B_160)=k1_xboole_0)), inference(resolution, [status(thm)], [c_790, c_22])).
% 4.63/1.80  tff(c_3312, plain, (![A_158, A_14]: (~r2_hidden('#skF_4'(A_158, A_158, A_14), k1_xboole_0) | k4_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_3240])).
% 4.63/1.80  tff(c_3335, plain, (![A_158, A_14]: (~r2_hidden('#skF_4'(A_158, A_158, A_14), k1_xboole_0) | k1_xboole_0=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3312])).
% 4.63/1.80  tff(c_3486, plain, (![B_165]: (k4_xboole_0(k1_xboole_0, B_165)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3357, c_3335])).
% 4.63/1.80  tff(c_625, plain, (![A_89]: (k4_xboole_0(A_89, A_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_520, c_597])).
% 4.63/1.80  tff(c_42, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k4_xboole_0(A_15, B_16), C_17)=k4_xboole_0(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.63/1.80  tff(c_661, plain, (![A_89, C_17]: (k4_xboole_0(A_89, k2_xboole_0(A_89, C_17))=k4_xboole_0(k1_xboole_0, C_17))), inference(superposition, [status(thm), theory('equality')], [c_625, c_42])).
% 4.63/1.80  tff(c_44, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_5', '#skF_6'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.63/1.80  tff(c_845, plain, (k4_xboole_0(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_661, c_44])).
% 4.63/1.80  tff(c_3750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3486, c_845])).
% 4.63/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.80  
% 4.63/1.80  Inference rules
% 4.63/1.80  ----------------------
% 4.63/1.80  #Ref     : 0
% 4.63/1.80  #Sup     : 880
% 4.63/1.80  #Fact    : 6
% 4.63/1.80  #Define  : 0
% 4.63/1.80  #Split   : 0
% 4.63/1.80  #Chain   : 0
% 4.63/1.80  #Close   : 0
% 4.63/1.80  
% 4.63/1.80  Ordering : KBO
% 4.63/1.80  
% 4.63/1.80  Simplification rules
% 4.63/1.80  ----------------------
% 4.63/1.80  #Subsume      : 185
% 4.63/1.80  #Demod        : 518
% 4.63/1.80  #Tautology    : 264
% 4.63/1.80  #SimpNegUnit  : 0
% 4.63/1.80  #BackRed      : 9
% 4.63/1.80  
% 4.63/1.80  #Partial instantiations: 0
% 4.63/1.80  #Strategies tried      : 1
% 4.63/1.80  
% 4.63/1.80  Timing (in seconds)
% 4.63/1.80  ----------------------
% 4.63/1.80  Preprocessing        : 0.27
% 4.63/1.80  Parsing              : 0.14
% 4.63/1.80  CNF conversion       : 0.02
% 4.63/1.80  Main loop            : 0.77
% 4.63/1.80  Inferencing          : 0.26
% 4.63/1.80  Reduction            : 0.24
% 4.63/1.80  Demodulation         : 0.19
% 4.63/1.80  BG Simplification    : 0.04
% 4.63/1.80  Subsumption          : 0.19
% 4.63/1.80  Abstraction          : 0.04
% 4.63/1.80  MUC search           : 0.00
% 4.63/1.80  Cooper               : 0.00
% 4.67/1.80  Total                : 1.07
% 4.67/1.80  Index Insertion      : 0.00
% 4.67/1.80  Index Deletion       : 0.00
% 4.67/1.80  Index Matching       : 0.00
% 4.67/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
