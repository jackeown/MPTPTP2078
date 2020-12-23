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
% DateTime   : Thu Dec  3 09:43:26 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  86 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_153,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_xboole_0(A_38,C_39)
      | ~ r1_xboole_0(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_160,plain,(
    ! [A_41] :
      ( r1_xboole_0(A_41,'#skF_5')
      | ~ r1_tarski(A_41,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_153])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_55,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_62,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_83,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_101,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_83])).

tff(c_108,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_101])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_119,plain,(
    ! [C_12] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_12,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_12])).

tff(c_143,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_165,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_160,c_143])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_165])).

tff(c_175,plain,(
    ! [C_42] : ~ r2_hidden(C_42,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_180,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_175])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_183,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_180,c_6])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n014.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:41:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.16  
% 1.86/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.16  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 1.86/1.16  
% 1.86/1.16  %Foreground sorts:
% 1.86/1.16  
% 1.86/1.16  
% 1.86/1.16  %Background operators:
% 1.86/1.16  
% 1.86/1.16  
% 1.86/1.16  %Foreground operators:
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.86/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.86/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.86/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.86/1.16  
% 1.86/1.17  tff(f_76, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.86/1.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.86/1.17  tff(f_67, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.86/1.17  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.86/1.17  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.86/1.17  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.86/1.17  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.86/1.17  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.86/1.17  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.86/1.17  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.17  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.86/1.17  tff(c_26, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.86/1.17  tff(c_153, plain, (![A_38, C_39, B_40]: (r1_xboole_0(A_38, C_39) | ~r1_xboole_0(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.86/1.17  tff(c_160, plain, (![A_41]: (r1_xboole_0(A_41, '#skF_5') | ~r1_tarski(A_41, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_153])).
% 1.86/1.17  tff(c_18, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.17  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.86/1.17  tff(c_55, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.86/1.17  tff(c_62, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_55])).
% 1.86/1.17  tff(c_83, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.86/1.17  tff(c_101, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_62, c_83])).
% 1.86/1.17  tff(c_108, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_101])).
% 1.86/1.17  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.86/1.17  tff(c_119, plain, (![C_12]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_12, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_108, c_12])).
% 1.86/1.17  tff(c_143, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_119])).
% 1.86/1.17  tff(c_165, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_160, c_143])).
% 1.86/1.17  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_165])).
% 1.86/1.17  tff(c_175, plain, (![C_42]: (~r2_hidden(C_42, '#skF_3'))), inference(splitRight, [status(thm)], [c_119])).
% 1.86/1.17  tff(c_180, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_175])).
% 1.86/1.17  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.17  tff(c_183, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_180, c_6])).
% 1.86/1.17  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_183])).
% 1.86/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  Inference rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Ref     : 0
% 1.86/1.17  #Sup     : 41
% 1.86/1.17  #Fact    : 0
% 1.86/1.17  #Define  : 0
% 1.86/1.17  #Split   : 2
% 1.86/1.17  #Chain   : 0
% 1.86/1.17  #Close   : 0
% 1.86/1.17  
% 1.86/1.17  Ordering : KBO
% 1.86/1.17  
% 1.86/1.17  Simplification rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Subsume      : 0
% 1.86/1.17  #Demod        : 5
% 1.86/1.17  #Tautology    : 20
% 1.86/1.17  #SimpNegUnit  : 1
% 1.86/1.17  #BackRed      : 0
% 1.86/1.17  
% 1.86/1.17  #Partial instantiations: 0
% 1.86/1.17  #Strategies tried      : 1
% 1.86/1.17  
% 1.86/1.17  Timing (in seconds)
% 1.86/1.17  ----------------------
% 1.86/1.17  Preprocessing        : 0.27
% 1.86/1.17  Parsing              : 0.15
% 1.86/1.17  CNF conversion       : 0.02
% 1.86/1.17  Main loop            : 0.14
% 1.86/1.17  Inferencing          : 0.06
% 1.86/1.17  Reduction            : 0.04
% 1.86/1.17  Demodulation         : 0.03
% 1.86/1.17  BG Simplification    : 0.01
% 1.86/1.17  Subsumption          : 0.02
% 1.86/1.17  Abstraction          : 0.01
% 1.86/1.17  MUC search           : 0.00
% 1.86/1.17  Cooper               : 0.00
% 1.86/1.17  Total                : 0.44
% 1.86/1.17  Index Insertion      : 0.00
% 1.86/1.17  Index Deletion       : 0.00
% 1.86/1.18  Index Matching       : 0.00
% 1.86/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
