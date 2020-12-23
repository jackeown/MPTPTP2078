%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:02 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   42 (  52 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  63 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_115,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden('#skF_1'(A_46,B_47),B_47)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_121,plain,(
    ! [A_48] : r1_tarski(A_48,A_48) ),
    inference(resolution,[status(thm)],[c_8,c_115])).

tff(c_16,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_89,plain,(
    ! [A_33,C_34,B_35] :
      ( r2_hidden(A_33,C_34)
      | ~ r1_tarski(k2_tarski(A_33,B_35),C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_92,plain,(
    ! [A_15,C_34] :
      ( r2_hidden(A_15,C_34)
      | ~ r1_tarski(k1_tarski(A_15),C_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_89])).

tff(c_135,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(resolution,[status(thm)],[c_121,c_92])).

tff(c_30,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(k1_tarski(A_21),B_22)
      | r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_172,plain,(
    ! [B_59,A_60,C_61] :
      ( ~ r1_xboole_0(B_59,A_60)
      | ~ r2_hidden(C_61,k3_xboole_0(A_60,B_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_185,plain,(
    ! [C_61] :
      ( ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_61,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_172])).

tff(c_220,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_223,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_220])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_223])).

tff(c_230,plain,(
    ! [C_71] : ~ r2_hidden(C_71,k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_239,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_135,c_230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:26:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.18/1.26  
% 2.18/1.26  %Foreground sorts:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Background operators:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Foreground operators:
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.18/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.18/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.18/1.26  
% 2.18/1.27  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.18/1.27  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.18/1.27  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.18/1.27  tff(f_72, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 2.18/1.27  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.18/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.18/1.27  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.18/1.27  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.18/1.27  tff(c_115, plain, (![A_46, B_47]: (~r2_hidden('#skF_1'(A_46, B_47), B_47) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.18/1.27  tff(c_121, plain, (![A_48]: (r1_tarski(A_48, A_48))), inference(resolution, [status(thm)], [c_8, c_115])).
% 2.18/1.27  tff(c_16, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.18/1.27  tff(c_89, plain, (![A_33, C_34, B_35]: (r2_hidden(A_33, C_34) | ~r1_tarski(k2_tarski(A_33, B_35), C_34))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.18/1.27  tff(c_92, plain, (![A_15, C_34]: (r2_hidden(A_15, C_34) | ~r1_tarski(k1_tarski(A_15), C_34))), inference(superposition, [status(thm), theory('equality')], [c_16, c_89])).
% 2.18/1.27  tff(c_135, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(resolution, [status(thm)], [c_121, c_92])).
% 2.18/1.27  tff(c_30, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.27  tff(c_22, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), B_22) | r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.18/1.27  tff(c_32, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.27  tff(c_94, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.18/1.27  tff(c_172, plain, (![B_59, A_60, C_61]: (~r1_xboole_0(B_59, A_60) | ~r2_hidden(C_61, k3_xboole_0(A_60, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_94])).
% 2.18/1.27  tff(c_185, plain, (![C_61]: (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_3') | ~r2_hidden(C_61, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_172])).
% 2.18/1.27  tff(c_220, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_185])).
% 2.18/1.27  tff(c_223, plain, (r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_220])).
% 2.18/1.27  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_223])).
% 2.18/1.27  tff(c_230, plain, (![C_71]: (~r2_hidden(C_71, k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_185])).
% 2.18/1.27  tff(c_239, plain, $false, inference(resolution, [status(thm)], [c_135, c_230])).
% 2.18/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  Inference rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Ref     : 0
% 2.18/1.27  #Sup     : 49
% 2.18/1.27  #Fact    : 0
% 2.18/1.27  #Define  : 0
% 2.18/1.27  #Split   : 2
% 2.18/1.27  #Chain   : 0
% 2.18/1.27  #Close   : 0
% 2.18/1.27  
% 2.18/1.27  Ordering : KBO
% 2.18/1.27  
% 2.18/1.27  Simplification rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Subsume      : 11
% 2.18/1.27  #Demod        : 2
% 2.18/1.27  #Tautology    : 20
% 2.18/1.27  #SimpNegUnit  : 1
% 2.18/1.27  #BackRed      : 0
% 2.18/1.27  
% 2.18/1.27  #Partial instantiations: 0
% 2.18/1.27  #Strategies tried      : 1
% 2.18/1.27  
% 2.18/1.27  Timing (in seconds)
% 2.18/1.27  ----------------------
% 2.18/1.27  Preprocessing        : 0.28
% 2.18/1.27  Parsing              : 0.15
% 2.18/1.27  CNF conversion       : 0.02
% 2.18/1.27  Main loop            : 0.17
% 2.18/1.27  Inferencing          : 0.07
% 2.18/1.27  Reduction            : 0.05
% 2.18/1.27  Demodulation         : 0.04
% 2.18/1.27  BG Simplification    : 0.01
% 2.18/1.27  Subsumption          : 0.03
% 2.18/1.27  Abstraction          : 0.01
% 2.18/1.27  MUC search           : 0.00
% 2.18/1.27  Cooper               : 0.00
% 2.18/1.27  Total                : 0.48
% 2.18/1.27  Index Insertion      : 0.00
% 2.18/1.27  Index Deletion       : 0.00
% 2.18/1.27  Index Matching       : 0.00
% 2.18/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
