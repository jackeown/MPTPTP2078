%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:45 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   38 (  52 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  63 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_60,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_62,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
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

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_133,plain,(
    ! [B_38,C_39,A_40] :
      ( r2_hidden(B_38,C_39)
      | ~ r1_tarski(k2_tarski(A_40,B_38),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_138,plain,(
    ! [B_38,A_40] : r2_hidden(B_38,k2_tarski(A_40,B_38)) ),
    inference(resolution,[status(thm)],[c_32,c_133])).

tff(c_46,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_147,plain,(
    ! [D_48,B_49,A_50] :
      ( ~ r2_hidden(D_48,B_49)
      | r2_hidden(D_48,k2_xboole_0(A_50,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_161,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,k2_tarski('#skF_4','#skF_5'))
      | r2_hidden(D_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_147])).

tff(c_179,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_138,c_161])).

tff(c_34,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_195,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_199,plain,(
    ! [C_59,A_60] :
      ( ~ r2_hidden(C_59,k1_xboole_0)
      | ~ r2_hidden(C_59,A_60) ) ),
    inference(resolution,[status(thm)],[c_34,c_195])).

tff(c_212,plain,(
    ! [A_60] : ~ r2_hidden('#skF_5',A_60) ),
    inference(resolution,[status(thm)],[c_179,c_199])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.28  
% 1.94/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.94/1.28  
% 1.94/1.28  %Foreground sorts:
% 1.94/1.28  
% 1.94/1.28  
% 1.94/1.28  %Background operators:
% 1.94/1.28  
% 1.94/1.28  
% 1.94/1.28  %Foreground operators:
% 1.94/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.94/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.94/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.28  tff('#skF_5', type, '#skF_5': $i).
% 1.94/1.28  tff('#skF_6', type, '#skF_6': $i).
% 1.94/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.94/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.94/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.94/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.28  
% 1.94/1.29  tff(f_60, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.94/1.29  tff(f_72, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.94/1.29  tff(f_76, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.94/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.94/1.29  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.94/1.29  tff(f_62, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.94/1.29  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.94/1.29  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.94/1.29  tff(c_133, plain, (![B_38, C_39, A_40]: (r2_hidden(B_38, C_39) | ~r1_tarski(k2_tarski(A_40, B_38), C_39))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.94/1.29  tff(c_138, plain, (![B_38, A_40]: (r2_hidden(B_38, k2_tarski(A_40, B_38)))), inference(resolution, [status(thm)], [c_32, c_133])).
% 1.94/1.29  tff(c_46, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.94/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.29  tff(c_86, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_46, c_2])).
% 1.94/1.29  tff(c_147, plain, (![D_48, B_49, A_50]: (~r2_hidden(D_48, B_49) | r2_hidden(D_48, k2_xboole_0(A_50, B_49)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.94/1.29  tff(c_161, plain, (![D_52]: (~r2_hidden(D_52, k2_tarski('#skF_4', '#skF_5')) | r2_hidden(D_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_86, c_147])).
% 1.94/1.29  tff(c_179, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_138, c_161])).
% 1.94/1.29  tff(c_34, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.94/1.29  tff(c_195, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, B_57) | ~r2_hidden(C_58, A_56))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.29  tff(c_199, plain, (![C_59, A_60]: (~r2_hidden(C_59, k1_xboole_0) | ~r2_hidden(C_59, A_60))), inference(resolution, [status(thm)], [c_34, c_195])).
% 1.94/1.29  tff(c_212, plain, (![A_60]: (~r2_hidden('#skF_5', A_60))), inference(resolution, [status(thm)], [c_179, c_199])).
% 1.94/1.29  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_179])).
% 1.94/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.29  
% 1.94/1.29  Inference rules
% 1.94/1.29  ----------------------
% 1.94/1.29  #Ref     : 0
% 1.94/1.29  #Sup     : 41
% 1.94/1.29  #Fact    : 0
% 1.94/1.29  #Define  : 0
% 1.94/1.29  #Split   : 0
% 1.94/1.29  #Chain   : 0
% 1.94/1.29  #Close   : 0
% 1.94/1.29  
% 1.94/1.29  Ordering : KBO
% 1.94/1.29  
% 1.94/1.29  Simplification rules
% 1.94/1.29  ----------------------
% 1.94/1.29  #Subsume      : 6
% 1.94/1.29  #Demod        : 6
% 1.94/1.29  #Tautology    : 22
% 1.94/1.29  #SimpNegUnit  : 1
% 1.94/1.29  #BackRed      : 1
% 1.94/1.29  
% 1.94/1.29  #Partial instantiations: 0
% 1.94/1.29  #Strategies tried      : 1
% 1.94/1.29  
% 1.94/1.29  Timing (in seconds)
% 1.94/1.29  ----------------------
% 1.94/1.29  Preprocessing        : 0.29
% 1.94/1.29  Parsing              : 0.15
% 1.94/1.29  CNF conversion       : 0.02
% 1.94/1.29  Main loop            : 0.17
% 1.94/1.29  Inferencing          : 0.05
% 1.94/1.29  Reduction            : 0.05
% 1.94/1.29  Demodulation         : 0.04
% 1.94/1.29  BG Simplification    : 0.01
% 1.94/1.30  Subsumption          : 0.04
% 1.94/1.30  Abstraction          : 0.01
% 1.94/1.30  MUC search           : 0.00
% 1.94/1.30  Cooper               : 0.00
% 1.94/1.30  Total                : 0.49
% 1.94/1.30  Index Insertion      : 0.00
% 1.94/1.30  Index Deletion       : 0.00
% 1.94/1.30  Index Matching       : 0.00
% 1.94/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
