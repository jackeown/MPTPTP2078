%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:15 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  67 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_setfam_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_110,plain,(
    ! [B_40,C_41,A_42] :
      ( r1_tarski(k1_setfam_1(B_40),C_41)
      | ~ r1_tarski(A_42,C_41)
      | ~ r2_hidden(A_42,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_113,plain,(
    ! [B_40,B_12] :
      ( r1_tarski(k1_setfam_1(B_40),B_12)
      | ~ r2_hidden(B_12,B_40) ) ),
    inference(resolution,[status(thm)],[c_18,c_110])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_83,plain,(
    ! [C_34,B_35,A_36] :
      ( r2_hidden(C_34,B_35)
      | ~ r2_hidden(C_34,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_137,plain,(
    ! [A_49,B_50,B_51] :
      ( r2_hidden('#skF_2'(A_49,B_50),B_51)
      | ~ r1_tarski(A_49,B_51)
      | r1_xboole_0(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_12,c_83])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_46,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,B_28)
      | ~ r2_hidden(C_29,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    ! [C_30] :
      ( ~ r2_hidden(C_30,'#skF_5')
      | ~ r2_hidden(C_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_46])).

tff(c_65,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_2'(A_6,'#skF_5'),'#skF_3')
      | r1_xboole_0(A_6,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_50])).

tff(c_175,plain,(
    ! [A_55] :
      ( ~ r1_tarski(A_55,'#skF_3')
      | r1_xboole_0(A_55,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_137,c_65])).

tff(c_22,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_182,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_175,c_22])).

tff(c_185,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_182])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.25  
% 1.96/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_setfam_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.96/1.25  
% 1.96/1.25  %Foreground sorts:
% 1.96/1.25  
% 1.96/1.25  
% 1.96/1.25  %Background operators:
% 1.96/1.25  
% 1.96/1.25  
% 1.96/1.25  %Foreground operators:
% 1.96/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.96/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.96/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.96/1.25  
% 2.04/1.26  tff(f_69, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_setfam_1)).
% 2.04/1.26  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.04/1.26  tff(f_62, axiom, (![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 2.04/1.26  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.04/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.04/1.26  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.04/1.26  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.26  tff(c_110, plain, (![B_40, C_41, A_42]: (r1_tarski(k1_setfam_1(B_40), C_41) | ~r1_tarski(A_42, C_41) | ~r2_hidden(A_42, B_40))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.04/1.26  tff(c_113, plain, (![B_40, B_12]: (r1_tarski(k1_setfam_1(B_40), B_12) | ~r2_hidden(B_12, B_40))), inference(resolution, [status(thm)], [c_18, c_110])).
% 2.04/1.26  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.04/1.26  tff(c_83, plain, (![C_34, B_35, A_36]: (r2_hidden(C_34, B_35) | ~r2_hidden(C_34, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.26  tff(c_137, plain, (![A_49, B_50, B_51]: (r2_hidden('#skF_2'(A_49, B_50), B_51) | ~r1_tarski(A_49, B_51) | r1_xboole_0(A_49, B_50))), inference(resolution, [status(thm)], [c_12, c_83])).
% 2.04/1.26  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.04/1.26  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.04/1.26  tff(c_46, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, B_28) | ~r2_hidden(C_29, A_27))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.04/1.26  tff(c_50, plain, (![C_30]: (~r2_hidden(C_30, '#skF_5') | ~r2_hidden(C_30, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_46])).
% 2.04/1.26  tff(c_65, plain, (![A_6]: (~r2_hidden('#skF_2'(A_6, '#skF_5'), '#skF_3') | r1_xboole_0(A_6, '#skF_5'))), inference(resolution, [status(thm)], [c_10, c_50])).
% 2.04/1.26  tff(c_175, plain, (![A_55]: (~r1_tarski(A_55, '#skF_3') | r1_xboole_0(A_55, '#skF_5'))), inference(resolution, [status(thm)], [c_137, c_65])).
% 2.04/1.26  tff(c_22, plain, (~r1_xboole_0(k1_setfam_1('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.04/1.26  tff(c_182, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_175, c_22])).
% 2.04/1.26  tff(c_185, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_113, c_182])).
% 2.04/1.26  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_185])).
% 2.04/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.26  
% 2.04/1.26  Inference rules
% 2.04/1.26  ----------------------
% 2.04/1.26  #Ref     : 0
% 2.04/1.26  #Sup     : 33
% 2.04/1.26  #Fact    : 0
% 2.04/1.26  #Define  : 0
% 2.04/1.26  #Split   : 1
% 2.04/1.26  #Chain   : 0
% 2.04/1.26  #Close   : 0
% 2.04/1.26  
% 2.04/1.26  Ordering : KBO
% 2.04/1.26  
% 2.04/1.26  Simplification rules
% 2.04/1.26  ----------------------
% 2.04/1.26  #Subsume      : 2
% 2.04/1.26  #Demod        : 5
% 2.04/1.26  #Tautology    : 6
% 2.04/1.26  #SimpNegUnit  : 0
% 2.04/1.26  #BackRed      : 0
% 2.04/1.26  
% 2.04/1.26  #Partial instantiations: 0
% 2.04/1.26  #Strategies tried      : 1
% 2.04/1.26  
% 2.04/1.26  Timing (in seconds)
% 2.04/1.26  ----------------------
% 2.04/1.27  Preprocessing        : 0.27
% 2.04/1.27  Parsing              : 0.15
% 2.04/1.27  CNF conversion       : 0.02
% 2.04/1.27  Main loop            : 0.22
% 2.04/1.27  Inferencing          : 0.10
% 2.04/1.27  Reduction            : 0.05
% 2.04/1.27  Demodulation         : 0.03
% 2.04/1.27  BG Simplification    : 0.01
% 2.04/1.27  Subsumption          : 0.05
% 2.04/1.27  Abstraction          : 0.01
% 2.04/1.27  MUC search           : 0.00
% 2.04/1.27  Cooper               : 0.00
% 2.04/1.27  Total                : 0.52
% 2.04/1.27  Index Insertion      : 0.00
% 2.04/1.27  Index Deletion       : 0.00
% 2.04/1.27  Index Matching       : 0.00
% 2.04/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
