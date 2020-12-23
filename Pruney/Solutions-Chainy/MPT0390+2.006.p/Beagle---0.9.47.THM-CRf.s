%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:14 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  33 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_tarski(A,C) )
       => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_12,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_setfam_1(B_7),A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ! [B_16,A_17] :
      ( k2_xboole_0(k1_setfam_1(B_16),A_17) = A_17
      | ~ r2_hidden(A_17,B_16) ) ),
    inference(resolution,[status(thm)],[c_6,c_18])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [B_18,C_19,A_20] :
      ( r1_tarski(k1_setfam_1(B_18),C_19)
      | ~ r1_tarski(A_20,C_19)
      | ~ r2_hidden(A_20,B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2])).

tff(c_55,plain,(
    ! [B_21] :
      ( r1_tarski(k1_setfam_1(B_21),'#skF_3')
      | ~ r2_hidden('#skF_1',B_21) ) ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_8,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_8])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.20/0.35  % Computer   : n022.cluster.edu
% 0.20/0.35  % Model      : x86_64 x86_64
% 0.20/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.20/0.35  % Memory     : 8042.1875MB
% 0.20/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % DateTime   : Tue Dec  1 13:40:40 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.47  
% 2.04/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.48  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.04/1.48  
% 2.04/1.48  %Foreground sorts:
% 2.04/1.48  
% 2.04/1.48  
% 2.04/1.48  %Background operators:
% 2.04/1.48  
% 2.04/1.48  
% 2.04/1.48  %Foreground operators:
% 2.04/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.04/1.48  
% 2.08/1.49  tff(f_44, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 2.08/1.49  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.08/1.49  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.08/1.49  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.08/1.49  tff(c_12, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.49  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.49  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k1_setfam_1(B_7), A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.49  tff(c_18, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.49  tff(c_36, plain, (![B_16, A_17]: (k2_xboole_0(k1_setfam_1(B_16), A_17)=A_17 | ~r2_hidden(A_17, B_16))), inference(resolution, [status(thm)], [c_6, c_18])).
% 2.08/1.49  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.49  tff(c_48, plain, (![B_18, C_19, A_20]: (r1_tarski(k1_setfam_1(B_18), C_19) | ~r1_tarski(A_20, C_19) | ~r2_hidden(A_20, B_18))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2])).
% 2.08/1.49  tff(c_55, plain, (![B_21]: (r1_tarski(k1_setfam_1(B_21), '#skF_3') | ~r2_hidden('#skF_1', B_21))), inference(resolution, [status(thm)], [c_10, c_48])).
% 2.08/1.49  tff(c_8, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.49  tff(c_63, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_55, c_8])).
% 2.08/1.49  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_63])).
% 2.08/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.49  
% 2.08/1.49  Inference rules
% 2.08/1.49  ----------------------
% 2.08/1.49  #Ref     : 0
% 2.08/1.49  #Sup     : 14
% 2.08/1.49  #Fact    : 0
% 2.08/1.49  #Define  : 0
% 2.08/1.49  #Split   : 0
% 2.08/1.49  #Chain   : 0
% 2.08/1.49  #Close   : 0
% 2.08/1.49  
% 2.08/1.49  Ordering : KBO
% 2.08/1.49  
% 2.08/1.49  Simplification rules
% 2.08/1.49  ----------------------
% 2.08/1.49  #Subsume      : 0
% 2.08/1.49  #Demod        : 1
% 2.08/1.49  #Tautology    : 4
% 2.08/1.49  #SimpNegUnit  : 0
% 2.08/1.49  #BackRed      : 0
% 2.08/1.49  
% 2.08/1.49  #Partial instantiations: 0
% 2.08/1.49  #Strategies tried      : 1
% 2.08/1.49  
% 2.08/1.49  Timing (in seconds)
% 2.08/1.49  ----------------------
% 2.08/1.50  Preprocessing        : 0.39
% 2.08/1.50  Parsing              : 0.21
% 2.08/1.50  CNF conversion       : 0.03
% 2.08/1.50  Main loop            : 0.18
% 2.08/1.50  Inferencing          : 0.08
% 2.08/1.50  Reduction            : 0.04
% 2.08/1.50  Demodulation         : 0.03
% 2.08/1.50  BG Simplification    : 0.02
% 2.08/1.50  Subsumption          : 0.03
% 2.08/1.50  Abstraction          : 0.01
% 2.08/1.50  MUC search           : 0.00
% 2.08/1.50  Cooper               : 0.00
% 2.08/1.50  Total                : 0.61
% 2.08/1.50  Index Insertion      : 0.00
% 2.08/1.50  Index Deletion       : 0.00
% 2.08/1.50  Index Matching       : 0.00
% 2.08/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
