%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:29 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   32 (  73 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 ( 142 expanded)
%              Number of equality atoms :   11 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_34,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_150,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_2'(A_53,B_54),A_53)
      | r2_hidden('#skF_3'(A_53,B_54),B_54)
      | k3_tarski(A_53) = B_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_5,C_20] :
      ( r2_hidden('#skF_4'(A_5,k3_tarski(A_5),C_20),A_5)
      | ~ r2_hidden(C_20,k3_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_49,plain,(
    ! [A_30,C_31,B_32] :
      ( ~ r2_hidden(A_30,C_31)
      | ~ r2_hidden(A_30,B_32)
      | ~ r2_hidden(A_30,k5_xboole_0(B_32,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [A_36,A_37] :
      ( ~ r2_hidden(A_36,k1_xboole_0)
      | ~ r2_hidden(A_36,A_37)
      | ~ r2_hidden(A_36,A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_49])).

tff(c_111,plain,(
    ! [C_48,A_49] :
      ( ~ r2_hidden('#skF_4'(k1_xboole_0,k3_tarski(k1_xboole_0),C_48),A_49)
      | ~ r2_hidden(C_48,k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_18,c_69])).

tff(c_131,plain,(
    ! [C_20] : ~ r2_hidden(C_20,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_18,c_111])).

tff(c_317,plain,(
    ! [A_60] :
      ( r2_hidden('#skF_2'(A_60,k3_tarski(k1_xboole_0)),A_60)
      | k3_tarski(k1_xboole_0) = k3_tarski(A_60) ) ),
    inference(resolution,[status(thm)],[c_150,c_131])).

tff(c_363,plain,(
    k3_tarski(k3_tarski(k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_317,c_131])).

tff(c_205,plain,(
    ! [B_54] :
      ( r2_hidden('#skF_3'(k3_tarski(k1_xboole_0),B_54),B_54)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_54 ) ),
    inference(resolution,[status(thm)],[c_150,c_131])).

tff(c_398,plain,(
    ! [B_63] :
      ( r2_hidden('#skF_3'(k3_tarski(k1_xboole_0),B_63),B_63)
      | k3_tarski(k1_xboole_0) = B_63 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_205])).

tff(c_58,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden(A_33,B_34)
      | ~ r2_hidden(A_33,C_35)
      | r2_hidden(A_33,k5_xboole_0(B_34,C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    ! [A_33,A_4] :
      ( r2_hidden(A_33,A_4)
      | ~ r2_hidden(A_33,k1_xboole_0)
      | r2_hidden(A_33,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_58])).

tff(c_409,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_3'(k3_tarski(k1_xboole_0),k1_xboole_0),A_4)
      | k3_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_398,c_66])).

tff(c_430,plain,(
    ! [A_64] : r2_hidden('#skF_3'(k3_tarski(k1_xboole_0),k1_xboole_0),A_64) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_409])).

tff(c_451,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_430,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  
% 2.08/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  %$ r2_hidden > k5_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.08/1.27  
% 2.08/1.27  %Foreground sorts:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Background operators:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Foreground operators:
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.08/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.08/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.27  
% 2.08/1.28  tff(f_46, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.08/1.28  tff(f_44, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.08/1.28  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.08/1.28  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.08/1.28  tff(c_34, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.28  tff(c_150, plain, (![A_53, B_54]: (r2_hidden('#skF_2'(A_53, B_54), A_53) | r2_hidden('#skF_3'(A_53, B_54), B_54) | k3_tarski(A_53)=B_54)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.28  tff(c_18, plain, (![A_5, C_20]: (r2_hidden('#skF_4'(A_5, k3_tarski(A_5), C_20), A_5) | ~r2_hidden(C_20, k3_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.28  tff(c_14, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.08/1.28  tff(c_49, plain, (![A_30, C_31, B_32]: (~r2_hidden(A_30, C_31) | ~r2_hidden(A_30, B_32) | ~r2_hidden(A_30, k5_xboole_0(B_32, C_31)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.28  tff(c_69, plain, (![A_36, A_37]: (~r2_hidden(A_36, k1_xboole_0) | ~r2_hidden(A_36, A_37) | ~r2_hidden(A_36, A_37))), inference(superposition, [status(thm), theory('equality')], [c_14, c_49])).
% 2.08/1.28  tff(c_111, plain, (![C_48, A_49]: (~r2_hidden('#skF_4'(k1_xboole_0, k3_tarski(k1_xboole_0), C_48), A_49) | ~r2_hidden(C_48, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_18, c_69])).
% 2.08/1.28  tff(c_131, plain, (![C_20]: (~r2_hidden(C_20, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_18, c_111])).
% 2.08/1.28  tff(c_317, plain, (![A_60]: (r2_hidden('#skF_2'(A_60, k3_tarski(k1_xboole_0)), A_60) | k3_tarski(k1_xboole_0)=k3_tarski(A_60))), inference(resolution, [status(thm)], [c_150, c_131])).
% 2.08/1.28  tff(c_363, plain, (k3_tarski(k3_tarski(k1_xboole_0))=k3_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_317, c_131])).
% 2.08/1.28  tff(c_205, plain, (![B_54]: (r2_hidden('#skF_3'(k3_tarski(k1_xboole_0), B_54), B_54) | k3_tarski(k3_tarski(k1_xboole_0))=B_54)), inference(resolution, [status(thm)], [c_150, c_131])).
% 2.08/1.28  tff(c_398, plain, (![B_63]: (r2_hidden('#skF_3'(k3_tarski(k1_xboole_0), B_63), B_63) | k3_tarski(k1_xboole_0)=B_63)), inference(demodulation, [status(thm), theory('equality')], [c_363, c_205])).
% 2.08/1.28  tff(c_58, plain, (![A_33, B_34, C_35]: (r2_hidden(A_33, B_34) | ~r2_hidden(A_33, C_35) | r2_hidden(A_33, k5_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.28  tff(c_66, plain, (![A_33, A_4]: (r2_hidden(A_33, A_4) | ~r2_hidden(A_33, k1_xboole_0) | r2_hidden(A_33, A_4))), inference(superposition, [status(thm), theory('equality')], [c_14, c_58])).
% 2.08/1.28  tff(c_409, plain, (![A_4]: (r2_hidden('#skF_3'(k3_tarski(k1_xboole_0), k1_xboole_0), A_4) | k3_tarski(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_398, c_66])).
% 2.08/1.28  tff(c_430, plain, (![A_64]: (r2_hidden('#skF_3'(k3_tarski(k1_xboole_0), k1_xboole_0), A_64))), inference(negUnitSimplification, [status(thm)], [c_34, c_409])).
% 2.08/1.28  tff(c_451, plain, $false, inference(resolution, [status(thm)], [c_430, c_131])).
% 2.08/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  Inference rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Ref     : 0
% 2.08/1.28  #Sup     : 87
% 2.08/1.28  #Fact    : 0
% 2.08/1.28  #Define  : 0
% 2.08/1.28  #Split   : 0
% 2.08/1.28  #Chain   : 0
% 2.08/1.28  #Close   : 0
% 2.08/1.28  
% 2.08/1.28  Ordering : KBO
% 2.08/1.28  
% 2.08/1.28  Simplification rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Subsume      : 17
% 2.08/1.28  #Demod        : 32
% 2.08/1.28  #Tautology    : 19
% 2.08/1.28  #SimpNegUnit  : 3
% 2.08/1.28  #BackRed      : 5
% 2.08/1.28  
% 2.08/1.28  #Partial instantiations: 0
% 2.08/1.28  #Strategies tried      : 1
% 2.08/1.28  
% 2.08/1.28  Timing (in seconds)
% 2.08/1.28  ----------------------
% 2.08/1.28  Preprocessing        : 0.25
% 2.08/1.28  Parsing              : 0.13
% 2.08/1.28  CNF conversion       : 0.02
% 2.08/1.28  Main loop            : 0.24
% 2.08/1.28  Inferencing          : 0.09
% 2.08/1.28  Reduction            : 0.06
% 2.08/1.28  Demodulation         : 0.04
% 2.08/1.28  BG Simplification    : 0.01
% 2.08/1.28  Subsumption          : 0.05
% 2.08/1.28  Abstraction          : 0.01
% 2.08/1.28  MUC search           : 0.00
% 2.08/1.28  Cooper               : 0.00
% 2.08/1.28  Total                : 0.51
% 2.08/1.28  Index Insertion      : 0.00
% 2.08/1.28  Index Deletion       : 0.00
% 2.08/1.28  Index Matching       : 0.00
% 2.08/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
