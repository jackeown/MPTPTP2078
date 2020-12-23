%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:10 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 101 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_40,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_1'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [A_46] : r1_tarski(A_46,A_46) ),
    inference(resolution,[status(thm)],[c_65,c_4])).

tff(c_42,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_112,plain,(
    ! [C_59,D_60,A_61] :
      ( r2_hidden(C_59,D_60)
      | ~ r2_hidden(D_60,A_61)
      | ~ r2_hidden(C_59,k1_setfam_1(A_61))
      | k1_xboole_0 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_127,plain,(
    ! [C_59] :
      ( r2_hidden(C_59,'#skF_7')
      | ~ r2_hidden(C_59,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_42,c_112])).

tff(c_142,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_14,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_xboole_0(A_41,k4_xboole_0(C_42,B_43))
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_63,plain,(
    ! [A_41,A_11] :
      ( r1_xboole_0(A_41,A_11)
      | ~ r1_tarski(A_41,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_60])).

tff(c_72,plain,(
    ! [A_49,B_50,C_51] :
      ( ~ r1_xboole_0(A_49,B_50)
      | ~ r2_hidden(C_51,B_50)
      | ~ r2_hidden(C_51,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_96,plain,(
    ! [C_56,A_57,A_58] :
      ( ~ r2_hidden(C_56,A_57)
      | ~ r2_hidden(C_56,A_58)
      | ~ r1_tarski(A_58,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_63,c_72])).

tff(c_128,plain,(
    ! [A_62] :
      ( ~ r2_hidden('#skF_7',A_62)
      | ~ r1_tarski(A_62,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42,c_96])).

tff(c_136,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_128])).

tff(c_144,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_136])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_144])).

tff(c_156,plain,(
    ! [C_64] :
      ( r2_hidden(C_64,'#skF_7')
      | ~ r2_hidden(C_64,k1_setfam_1('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_237,plain,(
    ! [B_73] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_8'),B_73),'#skF_7')
      | r1_tarski(k1_setfam_1('#skF_8'),B_73) ) ),
    inference(resolution,[status(thm)],[c_6,c_156])).

tff(c_247,plain,(
    r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_237,c_4])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:16:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.29/1.31  
% 2.29/1.31  %Foreground sorts:
% 2.29/1.31  
% 2.29/1.31  
% 2.29/1.31  %Background operators:
% 2.29/1.31  
% 2.29/1.31  
% 2.29/1.31  %Foreground operators:
% 2.29/1.31  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.29/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.29/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.29/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.31  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.29/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.29/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.29/1.31  
% 2.29/1.32  tff(f_80, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.29/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.29/1.32  tff(f_75, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.29/1.32  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.29/1.32  tff(f_56, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.29/1.32  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.29/1.32  tff(c_40, plain, (~r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.29/1.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.32  tff(c_65, plain, (![A_46, B_47]: (r2_hidden('#skF_1'(A_46, B_47), A_46) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.32  tff(c_70, plain, (![A_46]: (r1_tarski(A_46, A_46))), inference(resolution, [status(thm)], [c_65, c_4])).
% 2.29/1.32  tff(c_42, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.29/1.32  tff(c_112, plain, (![C_59, D_60, A_61]: (r2_hidden(C_59, D_60) | ~r2_hidden(D_60, A_61) | ~r2_hidden(C_59, k1_setfam_1(A_61)) | k1_xboole_0=A_61)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.29/1.32  tff(c_127, plain, (![C_59]: (r2_hidden(C_59, '#skF_7') | ~r2_hidden(C_59, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_42, c_112])).
% 2.29/1.32  tff(c_142, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_127])).
% 2.29/1.32  tff(c_14, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.32  tff(c_60, plain, (![A_41, C_42, B_43]: (r1_xboole_0(A_41, k4_xboole_0(C_42, B_43)) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.29/1.32  tff(c_63, plain, (![A_41, A_11]: (r1_xboole_0(A_41, A_11) | ~r1_tarski(A_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_60])).
% 2.29/1.32  tff(c_72, plain, (![A_49, B_50, C_51]: (~r1_xboole_0(A_49, B_50) | ~r2_hidden(C_51, B_50) | ~r2_hidden(C_51, A_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.29/1.32  tff(c_96, plain, (![C_56, A_57, A_58]: (~r2_hidden(C_56, A_57) | ~r2_hidden(C_56, A_58) | ~r1_tarski(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_63, c_72])).
% 2.29/1.32  tff(c_128, plain, (![A_62]: (~r2_hidden('#skF_7', A_62) | ~r1_tarski(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_96])).
% 2.29/1.32  tff(c_136, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_128])).
% 2.29/1.32  tff(c_144, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_136])).
% 2.29/1.32  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_144])).
% 2.29/1.32  tff(c_156, plain, (![C_64]: (r2_hidden(C_64, '#skF_7') | ~r2_hidden(C_64, k1_setfam_1('#skF_8')))), inference(splitRight, [status(thm)], [c_127])).
% 2.29/1.32  tff(c_237, plain, (![B_73]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_8'), B_73), '#skF_7') | r1_tarski(k1_setfam_1('#skF_8'), B_73))), inference(resolution, [status(thm)], [c_6, c_156])).
% 2.29/1.32  tff(c_247, plain, (r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_237, c_4])).
% 2.29/1.32  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_247])).
% 2.29/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.32  
% 2.29/1.32  Inference rules
% 2.29/1.32  ----------------------
% 2.29/1.32  #Ref     : 0
% 2.29/1.32  #Sup     : 48
% 2.29/1.32  #Fact    : 0
% 2.29/1.32  #Define  : 0
% 2.29/1.32  #Split   : 2
% 2.29/1.32  #Chain   : 0
% 2.29/1.32  #Close   : 0
% 2.29/1.32  
% 2.29/1.32  Ordering : KBO
% 2.29/1.32  
% 2.29/1.32  Simplification rules
% 2.29/1.32  ----------------------
% 2.29/1.32  #Subsume      : 4
% 2.29/1.32  #Demod        : 12
% 2.29/1.32  #Tautology    : 6
% 2.29/1.32  #SimpNegUnit  : 1
% 2.29/1.32  #BackRed      : 8
% 2.29/1.32  
% 2.29/1.32  #Partial instantiations: 0
% 2.29/1.32  #Strategies tried      : 1
% 2.29/1.32  
% 2.29/1.32  Timing (in seconds)
% 2.29/1.32  ----------------------
% 2.29/1.32  Preprocessing        : 0.30
% 2.29/1.32  Parsing              : 0.17
% 2.29/1.32  CNF conversion       : 0.02
% 2.29/1.32  Main loop            : 0.21
% 2.29/1.32  Inferencing          : 0.07
% 2.29/1.32  Reduction            : 0.05
% 2.29/1.32  Demodulation         : 0.04
% 2.29/1.32  BG Simplification    : 0.01
% 2.29/1.32  Subsumption          : 0.05
% 2.29/1.32  Abstraction          : 0.01
% 2.29/1.32  MUC search           : 0.00
% 2.29/1.32  Cooper               : 0.00
% 2.29/1.32  Total                : 0.54
% 2.29/1.32  Index Insertion      : 0.00
% 2.29/1.32  Index Deletion       : 0.00
% 2.29/1.32  Index Matching       : 0.00
% 2.29/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
