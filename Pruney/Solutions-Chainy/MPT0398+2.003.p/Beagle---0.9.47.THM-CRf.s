%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:31 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_setfam_1)).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),A_8)
      | r1_setfam_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ r1_xboole_0(A_24,B_25)
      | ~ r2_hidden(C_26,k3_xboole_0(A_24,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35,plain,(
    ! [A_6,C_26] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_26,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_48,plain,(
    ! [C_29] : ~ r2_hidden(C_29,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_35])).

tff(c_53,plain,(
    ! [B_9] : r1_setfam_1(k1_xboole_0,B_9) ),
    inference(resolution,[status(thm)],[c_16,c_48])).

tff(c_18,plain,(
    ~ r1_setfam_1(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:29:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.07  
% 1.59/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.08  %$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.59/1.08  
% 1.59/1.08  %Foreground sorts:
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  %Background operators:
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  %Foreground operators:
% 1.59/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.08  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.59/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.59/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.08  tff('#skF_4', type, '#skF_4': $i).
% 1.59/1.08  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.59/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.59/1.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.59/1.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.59/1.08  
% 1.65/1.08  tff(f_55, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.65/1.08  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.65/1.08  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.65/1.08  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.65/1.08  tff(f_58, negated_conjecture, ~(![A]: r1_setfam_1(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_setfam_1)).
% 1.65/1.08  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), A_8) | r1_setfam_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.65/1.08  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.65/1.09  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.09  tff(c_28, plain, (![A_24, B_25, C_26]: (~r1_xboole_0(A_24, B_25) | ~r2_hidden(C_26, k3_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.65/1.09  tff(c_35, plain, (![A_6, C_26]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_28])).
% 1.65/1.09  tff(c_48, plain, (![C_29]: (~r2_hidden(C_29, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_35])).
% 1.65/1.09  tff(c_53, plain, (![B_9]: (r1_setfam_1(k1_xboole_0, B_9))), inference(resolution, [status(thm)], [c_16, c_48])).
% 1.65/1.09  tff(c_18, plain, (~r1_setfam_1(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.65/1.09  tff(c_56, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_18])).
% 1.65/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.09  
% 1.65/1.09  Inference rules
% 1.65/1.09  ----------------------
% 1.65/1.09  #Ref     : 0
% 1.65/1.09  #Sup     : 7
% 1.65/1.09  #Fact    : 0
% 1.65/1.09  #Define  : 0
% 1.65/1.09  #Split   : 0
% 1.65/1.09  #Chain   : 0
% 1.65/1.09  #Close   : 0
% 1.65/1.09  
% 1.65/1.09  Ordering : KBO
% 1.65/1.09  
% 1.65/1.09  Simplification rules
% 1.65/1.09  ----------------------
% 1.65/1.09  #Subsume      : 0
% 1.65/1.09  #Demod        : 3
% 1.65/1.09  #Tautology    : 4
% 1.65/1.09  #SimpNegUnit  : 0
% 1.65/1.09  #BackRed      : 1
% 1.65/1.09  
% 1.65/1.09  #Partial instantiations: 0
% 1.65/1.09  #Strategies tried      : 1
% 1.65/1.09  
% 1.65/1.09  Timing (in seconds)
% 1.65/1.09  ----------------------
% 1.65/1.09  Preprocessing        : 0.25
% 1.65/1.09  Parsing              : 0.14
% 1.65/1.09  CNF conversion       : 0.02
% 1.65/1.09  Main loop            : 0.08
% 1.65/1.09  Inferencing          : 0.03
% 1.65/1.09  Reduction            : 0.02
% 1.65/1.09  Demodulation         : 0.02
% 1.65/1.09  BG Simplification    : 0.01
% 1.65/1.09  Subsumption          : 0.01
% 1.65/1.09  Abstraction          : 0.00
% 1.65/1.09  MUC search           : 0.00
% 1.65/1.09  Cooper               : 0.00
% 1.65/1.09  Total                : 0.35
% 1.65/1.09  Index Insertion      : 0.00
% 1.65/1.09  Index Deletion       : 0.00
% 1.65/1.09  Index Matching       : 0.00
% 1.65/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
