%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:10 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  72 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_50,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_71,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,(
    ! [B_44,A_43] : r2_hidden(B_44,k2_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_59,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,k3_tarski(B_23))
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_613,plain,(
    ! [A_120,A_121,B_122] :
      ( r1_tarski(A_120,k2_xboole_0(A_121,B_122))
      | ~ r2_hidden(A_120,k2_tarski(A_121,B_122)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_40])).

tff(c_621,plain,(
    ! [B_44,A_43] : r1_tarski(B_44,k2_xboole_0(A_43,B_44)) ),
    inference(resolution,[status(thm)],[c_77,c_613])).

tff(c_52,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_238,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_246,plain,
    ( k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_238])).

tff(c_370,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_370])).

tff(c_647,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_42,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [E_9,B_4,C_5] : r2_hidden(E_9,k1_enumset1(E_9,B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_83,plain,(
    ! [A_43,B_44] : r2_hidden(A_43,k2_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_14])).

tff(c_175,plain,(
    ! [A_55,C_56,B_57] :
      ( r2_hidden(A_55,C_56)
      | ~ r1_tarski(k2_tarski(A_55,B_57),C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_310,plain,(
    ! [A_78,B_79,B_80] :
      ( r2_hidden(A_78,k3_tarski(B_79))
      | ~ r2_hidden(k2_tarski(A_78,B_80),B_79) ) ),
    inference(resolution,[status(thm)],[c_40,c_175])).

tff(c_322,plain,(
    ! [A_78,B_80,B_44] : r2_hidden(A_78,k3_tarski(k2_tarski(k2_tarski(A_78,B_80),B_44))) ),
    inference(resolution,[status(thm)],[c_83,c_310])).

tff(c_342,plain,(
    ! [A_78,B_80,B_44] : r2_hidden(A_78,k2_xboole_0(k2_tarski(A_78,B_80),B_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_322])).

tff(c_654,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_342])).

tff(c_661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:39:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.36  
% 2.36/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.36  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.36/1.36  
% 2.36/1.36  %Foreground sorts:
% 2.36/1.36  
% 2.36/1.36  
% 2.36/1.36  %Background operators:
% 2.36/1.36  
% 2.36/1.36  
% 2.36/1.36  %Foreground operators:
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.36/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.36/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.36/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.36/1.36  
% 2.64/1.37  tff(f_71, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.64/1.37  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.64/1.37  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.64/1.37  tff(f_60, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.64/1.37  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.64/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.64/1.37  tff(f_66, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.64/1.37  tff(c_50, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.64/1.37  tff(c_71, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.64/1.37  tff(c_10, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.64/1.37  tff(c_77, plain, (![B_44, A_43]: (r2_hidden(B_44, k2_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_10])).
% 2.64/1.37  tff(c_59, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.64/1.37  tff(c_40, plain, (![A_22, B_23]: (r1_tarski(A_22, k3_tarski(B_23)) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.64/1.37  tff(c_613, plain, (![A_120, A_121, B_122]: (r1_tarski(A_120, k2_xboole_0(A_121, B_122)) | ~r2_hidden(A_120, k2_tarski(A_121, B_122)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_40])).
% 2.64/1.37  tff(c_621, plain, (![B_44, A_43]: (r1_tarski(B_44, k2_xboole_0(A_43, B_44)))), inference(resolution, [status(thm)], [c_77, c_613])).
% 2.64/1.37  tff(c_52, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.64/1.37  tff(c_238, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.37  tff(c_246, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_238])).
% 2.64/1.37  tff(c_370, plain, (~r1_tarski('#skF_5', k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_246])).
% 2.64/1.37  tff(c_646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_621, c_370])).
% 2.64/1.37  tff(c_647, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_246])).
% 2.64/1.37  tff(c_42, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.64/1.37  tff(c_14, plain, (![E_9, B_4, C_5]: (r2_hidden(E_9, k1_enumset1(E_9, B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.64/1.37  tff(c_83, plain, (![A_43, B_44]: (r2_hidden(A_43, k2_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_14])).
% 2.64/1.37  tff(c_175, plain, (![A_55, C_56, B_57]: (r2_hidden(A_55, C_56) | ~r1_tarski(k2_tarski(A_55, B_57), C_56))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.64/1.37  tff(c_310, plain, (![A_78, B_79, B_80]: (r2_hidden(A_78, k3_tarski(B_79)) | ~r2_hidden(k2_tarski(A_78, B_80), B_79))), inference(resolution, [status(thm)], [c_40, c_175])).
% 2.64/1.37  tff(c_322, plain, (![A_78, B_80, B_44]: (r2_hidden(A_78, k3_tarski(k2_tarski(k2_tarski(A_78, B_80), B_44))))), inference(resolution, [status(thm)], [c_83, c_310])).
% 2.64/1.37  tff(c_342, plain, (![A_78, B_80, B_44]: (r2_hidden(A_78, k2_xboole_0(k2_tarski(A_78, B_80), B_44)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_322])).
% 2.64/1.37  tff(c_654, plain, (r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_647, c_342])).
% 2.64/1.37  tff(c_661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_654])).
% 2.64/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.37  
% 2.64/1.37  Inference rules
% 2.64/1.37  ----------------------
% 2.64/1.37  #Ref     : 0
% 2.64/1.37  #Sup     : 125
% 2.64/1.37  #Fact    : 0
% 2.64/1.37  #Define  : 0
% 2.64/1.37  #Split   : 1
% 2.64/1.37  #Chain   : 0
% 2.64/1.37  #Close   : 0
% 2.64/1.37  
% 2.64/1.37  Ordering : KBO
% 2.64/1.37  
% 2.64/1.37  Simplification rules
% 2.64/1.37  ----------------------
% 2.64/1.37  #Subsume      : 0
% 2.64/1.37  #Demod        : 67
% 2.64/1.37  #Tautology    : 75
% 2.64/1.37  #SimpNegUnit  : 1
% 2.64/1.37  #BackRed      : 2
% 2.64/1.37  
% 2.64/1.37  #Partial instantiations: 0
% 2.64/1.37  #Strategies tried      : 1
% 2.64/1.37  
% 2.64/1.37  Timing (in seconds)
% 2.64/1.37  ----------------------
% 2.64/1.38  Preprocessing        : 0.32
% 2.64/1.38  Parsing              : 0.16
% 2.64/1.38  CNF conversion       : 0.02
% 2.64/1.38  Main loop            : 0.28
% 2.64/1.38  Inferencing          : 0.10
% 2.64/1.38  Reduction            : 0.10
% 2.64/1.38  Demodulation         : 0.08
% 2.64/1.38  BG Simplification    : 0.02
% 2.64/1.38  Subsumption          : 0.05
% 2.64/1.38  Abstraction          : 0.02
% 2.64/1.38  MUC search           : 0.00
% 2.64/1.38  Cooper               : 0.00
% 2.64/1.38  Total                : 0.63
% 2.64/1.38  Index Insertion      : 0.00
% 2.64/1.38  Index Deletion       : 0.00
% 2.64/1.38  Index Matching       : 0.00
% 2.64/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
