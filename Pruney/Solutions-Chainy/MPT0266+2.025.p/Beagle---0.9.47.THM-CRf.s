%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:29 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   46 (  47 expanded)
%              Number of leaves         :   31 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  42 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_56,axiom,(
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

tff(c_80,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_178,plain,(
    ! [A_97,B_98] : k1_enumset1(A_97,A_97,B_98) = k2_tarski(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    ! [E_29,B_24,C_25] : r2_hidden(E_29,k1_enumset1(E_29,B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_184,plain,(
    ! [A_97,B_98] : r2_hidden(A_97,k2_tarski(A_97,B_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_40])).

tff(c_1141,plain,(
    ! [A_152,B_153,C_154] :
      ( r2_hidden(A_152,B_153)
      | ~ r2_hidden(A_152,C_154)
      | r2_hidden(A_152,k5_xboole_0(B_153,C_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_157,plain,(
    ! [A_94,B_95] : r1_xboole_0(k3_xboole_0(A_94,B_95),k5_xboole_0(A_94,B_95)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_160,plain,(
    r1_xboole_0(k2_tarski('#skF_4','#skF_5'),k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_157])).

tff(c_173,plain,(
    r1_xboole_0(k2_tarski('#skF_4','#skF_5'),k5_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_160])).

tff(c_253,plain,(
    ! [A_113,B_114,C_115] :
      ( ~ r1_xboole_0(A_113,B_114)
      | ~ r2_hidden(C_115,B_114)
      | ~ r2_hidden(C_115,A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_263,plain,(
    ! [C_115] :
      ( ~ r2_hidden(C_115,k5_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')))
      | ~ r2_hidden(C_115,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_173,c_253])).

tff(c_1272,plain,(
    ! [A_159] :
      ( r2_hidden(A_159,'#skF_6')
      | ~ r2_hidden(A_159,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1141,c_263])).

tff(c_1288,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_184,c_1272])).

tff(c_1295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.52  
% 3.24/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.53  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.24/1.53  
% 3.24/1.53  %Foreground sorts:
% 3.24/1.53  
% 3.24/1.53  
% 3.24/1.53  %Background operators:
% 3.24/1.53  
% 3.24/1.53  
% 3.24/1.53  %Foreground operators:
% 3.24/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.24/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.24/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.24/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.24/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.24/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.24/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.24/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.24/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.24/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.24/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.24/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.24/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.24/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.24/1.53  
% 3.28/1.53  tff(f_106, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 3.28/1.53  tff(f_89, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.28/1.53  tff(f_79, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.28/1.53  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.28/1.53  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.28/1.53  tff(f_58, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.28/1.53  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.28/1.53  tff(c_80, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.28/1.53  tff(c_178, plain, (![A_97, B_98]: (k1_enumset1(A_97, A_97, B_98)=k2_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.28/1.53  tff(c_40, plain, (![E_29, B_24, C_25]: (r2_hidden(E_29, k1_enumset1(E_29, B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.28/1.53  tff(c_184, plain, (![A_97, B_98]: (r2_hidden(A_97, k2_tarski(A_97, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_178, c_40])).
% 3.28/1.53  tff(c_1141, plain, (![A_152, B_153, C_154]: (r2_hidden(A_152, B_153) | ~r2_hidden(A_152, C_154) | r2_hidden(A_152, k5_xboole_0(B_153, C_154)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.28/1.53  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.28/1.53  tff(c_82, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.28/1.53  tff(c_157, plain, (![A_94, B_95]: (r1_xboole_0(k3_xboole_0(A_94, B_95), k5_xboole_0(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.53  tff(c_160, plain, (r1_xboole_0(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_157])).
% 3.28/1.53  tff(c_173, plain, (r1_xboole_0(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_160])).
% 3.28/1.53  tff(c_253, plain, (![A_113, B_114, C_115]: (~r1_xboole_0(A_113, B_114) | ~r2_hidden(C_115, B_114) | ~r2_hidden(C_115, A_113))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.28/1.53  tff(c_263, plain, (![C_115]: (~r2_hidden(C_115, k5_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))) | ~r2_hidden(C_115, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_173, c_253])).
% 3.28/1.53  tff(c_1272, plain, (![A_159]: (r2_hidden(A_159, '#skF_6') | ~r2_hidden(A_159, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_1141, c_263])).
% 3.28/1.53  tff(c_1288, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_184, c_1272])).
% 3.28/1.53  tff(c_1295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1288])).
% 3.28/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.53  
% 3.28/1.53  Inference rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Ref     : 0
% 3.28/1.53  #Sup     : 303
% 3.28/1.53  #Fact    : 0
% 3.28/1.53  #Define  : 0
% 3.28/1.53  #Split   : 0
% 3.28/1.54  #Chain   : 0
% 3.28/1.54  #Close   : 0
% 3.28/1.54  
% 3.28/1.54  Ordering : KBO
% 3.28/1.54  
% 3.28/1.54  Simplification rules
% 3.28/1.54  ----------------------
% 3.28/1.54  #Subsume      : 6
% 3.28/1.54  #Demod        : 139
% 3.28/1.54  #Tautology    : 184
% 3.28/1.54  #SimpNegUnit  : 1
% 3.28/1.54  #BackRed      : 0
% 3.28/1.54  
% 3.28/1.54  #Partial instantiations: 0
% 3.28/1.54  #Strategies tried      : 1
% 3.28/1.54  
% 3.28/1.54  Timing (in seconds)
% 3.28/1.54  ----------------------
% 3.28/1.54  Preprocessing        : 0.40
% 3.28/1.54  Parsing              : 0.23
% 3.28/1.54  CNF conversion       : 0.03
% 3.28/1.54  Main loop            : 0.37
% 3.28/1.54  Inferencing          : 0.12
% 3.28/1.54  Reduction            : 0.15
% 3.28/1.54  Demodulation         : 0.12
% 3.28/1.54  BG Simplification    : 0.03
% 3.28/1.54  Subsumption          : 0.06
% 3.28/1.54  Abstraction          : 0.02
% 3.28/1.54  MUC search           : 0.00
% 3.28/1.54  Cooper               : 0.00
% 3.28/1.54  Total                : 0.80
% 3.28/1.54  Index Insertion      : 0.00
% 3.28/1.54  Index Deletion       : 0.00
% 3.28/1.54  Index Matching       : 0.00
% 3.28/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
