%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:42 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  40 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k3_setfam_1,type,(
    k3_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k3_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k3_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(k3_setfam_1(A,A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_setfam_1)).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_setfam_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_17,B_18,D_44] :
      ( r2_hidden('#skF_7'(A_17,B_18,k3_setfam_1(A_17,B_18),D_44),A_17)
      | ~ r2_hidden(D_44,k3_setfam_1(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_192,plain,(
    ! [A_93,B_94,D_95] :
      ( k3_xboole_0('#skF_7'(A_93,B_94,k3_setfam_1(A_93,B_94),D_95),'#skF_8'(A_93,B_94,k3_setfam_1(A_93,B_94),D_95)) = D_95
      | ~ r2_hidden(D_95,k3_setfam_1(A_93,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_214,plain,(
    ! [D_96,A_97,B_98] :
      ( r1_tarski(D_96,'#skF_7'(A_97,B_98,k3_setfam_1(A_97,B_98),D_96))
      | ~ r2_hidden(D_96,k3_setfam_1(A_97,B_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_2])).

tff(c_10,plain,(
    ! [A_5,B_6,D_14] :
      ( ~ r1_tarski('#skF_1'(A_5,B_6),D_14)
      | ~ r2_hidden(D_14,B_6)
      | r1_setfam_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_374,plain,(
    ! [A_121,B_122,A_123,B_124] :
      ( ~ r2_hidden('#skF_7'(A_121,B_122,k3_setfam_1(A_121,B_122),'#skF_1'(A_123,B_124)),B_124)
      | r1_setfam_1(A_123,B_124)
      | ~ r2_hidden('#skF_1'(A_123,B_124),k3_setfam_1(A_121,B_122)) ) ),
    inference(resolution,[status(thm)],[c_214,c_10])).

tff(c_385,plain,(
    ! [A_130,A_131,B_132] :
      ( r1_setfam_1(A_130,A_131)
      | ~ r2_hidden('#skF_1'(A_130,A_131),k3_setfam_1(A_131,B_132)) ) ),
    inference(resolution,[status(thm)],[c_20,c_374])).

tff(c_390,plain,(
    ! [B_6,B_132] : r1_setfam_1(k3_setfam_1(B_6,B_132),B_6) ),
    inference(resolution,[status(thm)],[c_12,c_385])).

tff(c_38,plain,(
    ~ r1_setfam_1(k3_setfam_1('#skF_9','#skF_9'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.33  
% 2.26/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.33  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1
% 2.26/1.33  
% 2.26/1.33  %Foreground sorts:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Background operators:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Foreground operators:
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.33  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.26/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.33  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.26/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.26/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.33  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.26/1.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.26/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.26/1.33  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.26/1.33  tff('#skF_9', type, '#skF_9': $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.26/1.33  tff(k3_setfam_1, type, k3_setfam_1: ($i * $i) > $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.26/1.33  
% 2.26/1.34  tff(f_41, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.26/1.34  tff(f_53, axiom, (![A, B, C]: ((C = k3_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k3_xboole_0(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_setfam_1)).
% 2.26/1.34  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.26/1.34  tff(f_56, negated_conjecture, ~(![A]: r1_setfam_1(k3_setfam_1(A, A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_setfam_1)).
% 2.26/1.34  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_setfam_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.26/1.34  tff(c_20, plain, (![A_17, B_18, D_44]: (r2_hidden('#skF_7'(A_17, B_18, k3_setfam_1(A_17, B_18), D_44), A_17) | ~r2_hidden(D_44, k3_setfam_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.34  tff(c_192, plain, (![A_93, B_94, D_95]: (k3_xboole_0('#skF_7'(A_93, B_94, k3_setfam_1(A_93, B_94), D_95), '#skF_8'(A_93, B_94, k3_setfam_1(A_93, B_94), D_95))=D_95 | ~r2_hidden(D_95, k3_setfam_1(A_93, B_94)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.34  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.26/1.34  tff(c_214, plain, (![D_96, A_97, B_98]: (r1_tarski(D_96, '#skF_7'(A_97, B_98, k3_setfam_1(A_97, B_98), D_96)) | ~r2_hidden(D_96, k3_setfam_1(A_97, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_192, c_2])).
% 2.26/1.34  tff(c_10, plain, (![A_5, B_6, D_14]: (~r1_tarski('#skF_1'(A_5, B_6), D_14) | ~r2_hidden(D_14, B_6) | r1_setfam_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.26/1.34  tff(c_374, plain, (![A_121, B_122, A_123, B_124]: (~r2_hidden('#skF_7'(A_121, B_122, k3_setfam_1(A_121, B_122), '#skF_1'(A_123, B_124)), B_124) | r1_setfam_1(A_123, B_124) | ~r2_hidden('#skF_1'(A_123, B_124), k3_setfam_1(A_121, B_122)))), inference(resolution, [status(thm)], [c_214, c_10])).
% 2.26/1.34  tff(c_385, plain, (![A_130, A_131, B_132]: (r1_setfam_1(A_130, A_131) | ~r2_hidden('#skF_1'(A_130, A_131), k3_setfam_1(A_131, B_132)))), inference(resolution, [status(thm)], [c_20, c_374])).
% 2.26/1.34  tff(c_390, plain, (![B_6, B_132]: (r1_setfam_1(k3_setfam_1(B_6, B_132), B_6))), inference(resolution, [status(thm)], [c_12, c_385])).
% 2.26/1.34  tff(c_38, plain, (~r1_setfam_1(k3_setfam_1('#skF_9', '#skF_9'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.26/1.34  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_390, c_38])).
% 2.26/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.34  
% 2.26/1.34  Inference rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Ref     : 0
% 2.26/1.34  #Sup     : 86
% 2.26/1.34  #Fact    : 0
% 2.26/1.34  #Define  : 0
% 2.26/1.34  #Split   : 0
% 2.26/1.34  #Chain   : 0
% 2.26/1.34  #Close   : 0
% 2.26/1.34  
% 2.26/1.34  Ordering : KBO
% 2.26/1.34  
% 2.26/1.34  Simplification rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Subsume      : 0
% 2.26/1.34  #Demod        : 43
% 2.26/1.34  #Tautology    : 45
% 2.26/1.34  #SimpNegUnit  : 0
% 2.26/1.34  #BackRed      : 1
% 2.26/1.34  
% 2.26/1.34  #Partial instantiations: 0
% 2.26/1.34  #Strategies tried      : 1
% 2.26/1.34  
% 2.26/1.34  Timing (in seconds)
% 2.26/1.34  ----------------------
% 2.26/1.34  Preprocessing        : 0.30
% 2.26/1.35  Parsing              : 0.15
% 2.26/1.35  CNF conversion       : 0.03
% 2.26/1.35  Main loop            : 0.26
% 2.26/1.35  Inferencing          : 0.11
% 2.26/1.35  Reduction            : 0.08
% 2.26/1.35  Demodulation         : 0.06
% 2.26/1.35  BG Simplification    : 0.02
% 2.26/1.35  Subsumption          : 0.04
% 2.26/1.35  Abstraction          : 0.02
% 2.26/1.35  MUC search           : 0.00
% 2.26/1.35  Cooper               : 0.00
% 2.26/1.35  Total                : 0.59
% 2.26/1.35  Index Insertion      : 0.00
% 2.26/1.35  Index Deletion       : 0.00
% 2.26/1.35  Index Matching       : 0.00
% 2.26/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
