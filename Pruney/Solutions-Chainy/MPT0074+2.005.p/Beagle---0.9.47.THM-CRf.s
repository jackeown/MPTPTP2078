%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:27 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   46 (  55 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   57 (  83 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_5'(A_19),A_19)
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1282,plain,(
    ! [C_115,B_116,A_117] :
      ( r2_hidden(C_115,B_116)
      | ~ r2_hidden(C_115,A_117)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1288,plain,(
    ! [A_19,B_116] :
      ( r2_hidden('#skF_5'(A_19),B_116)
      | ~ r1_tarski(A_19,B_116)
      | k1_xboole_0 = A_19 ) ),
    inference(resolution,[status(thm)],[c_32,c_1282])).

tff(c_2168,plain,(
    ! [A_165,B_166] :
      ( r2_hidden('#skF_5'(A_165),B_166)
      | ~ r1_tarski(A_165,B_166)
      | k1_xboole_0 = A_165 ) ),
    inference(resolution,[status(thm)],[c_32,c_1282])).

tff(c_34,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_151,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,B_41)
      | ~ r2_hidden(C_42,k3_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_853,plain,(
    ! [A_89,B_90] :
      ( ~ r1_xboole_0(A_89,B_90)
      | k3_xboole_0(A_89,B_90) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_151])).

tff(c_866,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_853])).

tff(c_36,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_886,plain,(
    k4_xboole_0('#skF_7',k1_xboole_0) = k4_xboole_0('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_36])).

tff(c_891,plain,(
    k4_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_886])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_908,plain,(
    ! [D_11] :
      ( ~ r2_hidden(D_11,'#skF_8')
      | ~ r2_hidden(D_11,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_891,c_10])).

tff(c_2206,plain,(
    ! [A_167] :
      ( ~ r2_hidden('#skF_5'(A_167),'#skF_8')
      | ~ r1_tarski(A_167,'#skF_7')
      | k1_xboole_0 = A_167 ) ),
    inference(resolution,[status(thm)],[c_2168,c_908])).

tff(c_2317,plain,(
    ! [A_172] :
      ( ~ r1_tarski(A_172,'#skF_7')
      | ~ r1_tarski(A_172,'#skF_8')
      | k1_xboole_0 = A_172 ) ),
    inference(resolution,[status(thm)],[c_1288,c_2206])).

tff(c_2332,plain,
    ( ~ r1_tarski('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_2317])).

tff(c_2341,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2332])).

tff(c_2343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.58  
% 3.29/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_4
% 3.29/1.59  
% 3.29/1.59  %Foreground sorts:
% 3.29/1.59  
% 3.29/1.59  
% 3.29/1.59  %Background operators:
% 3.29/1.59  
% 3.29/1.59  
% 3.29/1.59  %Foreground operators:
% 3.29/1.59  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.29/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.29/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.29/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.29/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.29/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.29/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.29/1.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.29/1.59  
% 3.29/1.60  tff(f_83, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 3.29/1.60  tff(f_68, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.29/1.60  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.29/1.60  tff(f_70, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.29/1.60  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.29/1.60  tff(f_72, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.29/1.60  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.29/1.60  tff(c_40, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.29/1.60  tff(c_44, plain, (r1_tarski('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.29/1.60  tff(c_46, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.29/1.60  tff(c_32, plain, (![A_19]: (r2_hidden('#skF_5'(A_19), A_19) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.29/1.60  tff(c_1282, plain, (![C_115, B_116, A_117]: (r2_hidden(C_115, B_116) | ~r2_hidden(C_115, A_117) | ~r1_tarski(A_117, B_116))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.60  tff(c_1288, plain, (![A_19, B_116]: (r2_hidden('#skF_5'(A_19), B_116) | ~r1_tarski(A_19, B_116) | k1_xboole_0=A_19)), inference(resolution, [status(thm)], [c_32, c_1282])).
% 3.29/1.60  tff(c_2168, plain, (![A_165, B_166]: (r2_hidden('#skF_5'(A_165), B_166) | ~r1_tarski(A_165, B_166) | k1_xboole_0=A_165)), inference(resolution, [status(thm)], [c_32, c_1282])).
% 3.29/1.60  tff(c_34, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.29/1.60  tff(c_42, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.29/1.60  tff(c_151, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, B_41) | ~r2_hidden(C_42, k3_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.29/1.60  tff(c_853, plain, (![A_89, B_90]: (~r1_xboole_0(A_89, B_90) | k3_xboole_0(A_89, B_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_151])).
% 3.29/1.60  tff(c_866, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_853])).
% 3.29/1.60  tff(c_36, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.29/1.60  tff(c_886, plain, (k4_xboole_0('#skF_7', k1_xboole_0)=k4_xboole_0('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_866, c_36])).
% 3.29/1.60  tff(c_891, plain, (k4_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_886])).
% 3.29/1.60  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.29/1.60  tff(c_908, plain, (![D_11]: (~r2_hidden(D_11, '#skF_8') | ~r2_hidden(D_11, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_891, c_10])).
% 3.29/1.60  tff(c_2206, plain, (![A_167]: (~r2_hidden('#skF_5'(A_167), '#skF_8') | ~r1_tarski(A_167, '#skF_7') | k1_xboole_0=A_167)), inference(resolution, [status(thm)], [c_2168, c_908])).
% 3.29/1.60  tff(c_2317, plain, (![A_172]: (~r1_tarski(A_172, '#skF_7') | ~r1_tarski(A_172, '#skF_8') | k1_xboole_0=A_172)), inference(resolution, [status(thm)], [c_1288, c_2206])).
% 3.29/1.60  tff(c_2332, plain, (~r1_tarski('#skF_6', '#skF_8') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_46, c_2317])).
% 3.29/1.60  tff(c_2341, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2332])).
% 3.29/1.60  tff(c_2343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_2341])).
% 3.29/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.60  
% 3.29/1.60  Inference rules
% 3.29/1.60  ----------------------
% 3.29/1.60  #Ref     : 0
% 3.29/1.60  #Sup     : 560
% 3.29/1.60  #Fact    : 0
% 3.29/1.60  #Define  : 0
% 3.29/1.60  #Split   : 11
% 3.29/1.60  #Chain   : 0
% 3.29/1.60  #Close   : 0
% 3.29/1.60  
% 3.29/1.60  Ordering : KBO
% 3.29/1.60  
% 3.29/1.60  Simplification rules
% 3.29/1.60  ----------------------
% 3.29/1.60  #Subsume      : 89
% 3.29/1.60  #Demod        : 296
% 3.29/1.60  #Tautology    : 304
% 3.29/1.60  #SimpNegUnit  : 38
% 3.29/1.60  #BackRed      : 3
% 3.29/1.60  
% 3.29/1.60  #Partial instantiations: 0
% 3.29/1.60  #Strategies tried      : 1
% 3.29/1.60  
% 3.29/1.60  Timing (in seconds)
% 3.29/1.60  ----------------------
% 3.29/1.60  Preprocessing        : 0.30
% 3.29/1.60  Parsing              : 0.16
% 3.29/1.60  CNF conversion       : 0.02
% 3.29/1.60  Main loop            : 0.54
% 3.29/1.60  Inferencing          : 0.20
% 3.29/1.60  Reduction            : 0.18
% 3.29/1.60  Demodulation         : 0.12
% 3.29/1.60  BG Simplification    : 0.02
% 3.29/1.60  Subsumption          : 0.10
% 3.29/1.60  Abstraction          : 0.02
% 3.29/1.60  MUC search           : 0.00
% 3.29/1.60  Cooper               : 0.00
% 3.29/1.60  Total                : 0.87
% 3.29/1.60  Index Insertion      : 0.00
% 3.29/1.60  Index Deletion       : 0.00
% 3.29/1.60  Index Matching       : 0.00
% 3.29/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
