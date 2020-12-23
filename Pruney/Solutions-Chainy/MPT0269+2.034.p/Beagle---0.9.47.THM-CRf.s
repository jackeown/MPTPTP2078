%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:48 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  65 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,k1_tarski(B_44)) = A_43
      | r2_hidden(B_44,A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_150,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_34])).

tff(c_165,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_150])).

tff(c_14,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_224,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(k2_tarski(A_57,B_58),C_59)
      | ~ r2_hidden(B_58,C_59)
      | ~ r2_hidden(A_57,C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_273,plain,(
    ! [A_65,C_66] :
      ( r1_tarski(k1_tarski(A_65),C_66)
      | ~ r2_hidden(A_65,C_66)
      | ~ r2_hidden(A_65,C_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_224])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_288,plain,(
    ! [A_65,C_66] :
      ( k4_xboole_0(k1_tarski(A_65),C_66) = k1_xboole_0
      | ~ r2_hidden(A_65,C_66) ) ),
    inference(resolution,[status(thm)],[c_273,c_10])).

tff(c_30,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_171,plain,(
    ! [B_45,A_46] :
      ( B_45 = A_46
      | ~ r1_tarski(B_45,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_257,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ r1_tarski(B_63,A_64)
      | k4_xboole_0(A_64,B_63) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_171])).

tff(c_335,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | k4_xboole_0(B_71,A_72) != k1_xboole_0
      | k4_xboole_0(A_72,B_71) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_257])).

tff(c_343,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k4_xboole_0(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_335])).

tff(c_351,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_343])).

tff(c_354,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_351])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.27  
% 1.97/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.28  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.97/1.28  
% 1.97/1.28  %Foreground sorts:
% 1.97/1.28  
% 1.97/1.28  
% 1.97/1.28  %Background operators:
% 1.97/1.28  
% 1.97/1.28  
% 1.97/1.28  %Foreground operators:
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.97/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.28  
% 1.97/1.29  tff(f_64, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.97/1.29  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.97/1.29  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.97/1.29  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.97/1.29  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.97/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.97/1.29  tff(c_32, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.29  tff(c_137, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k1_tarski(B_44))=A_43 | r2_hidden(B_44, A_43))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.97/1.29  tff(c_34, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.29  tff(c_150, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_137, c_34])).
% 1.97/1.29  tff(c_165, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_150])).
% 1.97/1.29  tff(c_14, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.97/1.29  tff(c_224, plain, (![A_57, B_58, C_59]: (r1_tarski(k2_tarski(A_57, B_58), C_59) | ~r2_hidden(B_58, C_59) | ~r2_hidden(A_57, C_59))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.97/1.29  tff(c_273, plain, (![A_65, C_66]: (r1_tarski(k1_tarski(A_65), C_66) | ~r2_hidden(A_65, C_66) | ~r2_hidden(A_65, C_66))), inference(superposition, [status(thm), theory('equality')], [c_14, c_224])).
% 1.97/1.29  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.29  tff(c_288, plain, (![A_65, C_66]: (k4_xboole_0(k1_tarski(A_65), C_66)=k1_xboole_0 | ~r2_hidden(A_65, C_66))), inference(resolution, [status(thm)], [c_273, c_10])).
% 1.97/1.29  tff(c_30, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.29  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.29  tff(c_171, plain, (![B_45, A_46]: (B_45=A_46 | ~r1_tarski(B_45, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.29  tff(c_257, plain, (![B_63, A_64]: (B_63=A_64 | ~r1_tarski(B_63, A_64) | k4_xboole_0(A_64, B_63)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_171])).
% 1.97/1.29  tff(c_335, plain, (![B_71, A_72]: (B_71=A_72 | k4_xboole_0(B_71, A_72)!=k1_xboole_0 | k4_xboole_0(A_72, B_71)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_257])).
% 1.97/1.29  tff(c_343, plain, (k1_tarski('#skF_2')='#skF_1' | k4_xboole_0(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34, c_335])).
% 1.97/1.29  tff(c_351, plain, (k4_xboole_0(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_30, c_343])).
% 1.97/1.29  tff(c_354, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_288, c_351])).
% 1.97/1.29  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_354])).
% 1.97/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.29  
% 1.97/1.29  Inference rules
% 1.97/1.29  ----------------------
% 1.97/1.29  #Ref     : 0
% 1.97/1.29  #Sup     : 69
% 1.97/1.29  #Fact    : 0
% 1.97/1.29  #Define  : 0
% 1.97/1.29  #Split   : 0
% 1.97/1.29  #Chain   : 0
% 1.97/1.29  #Close   : 0
% 1.97/1.29  
% 1.97/1.29  Ordering : KBO
% 1.97/1.29  
% 1.97/1.29  Simplification rules
% 1.97/1.29  ----------------------
% 1.97/1.29  #Subsume      : 8
% 1.97/1.29  #Demod        : 17
% 1.97/1.29  #Tautology    : 37
% 1.97/1.29  #SimpNegUnit  : 7
% 1.97/1.29  #BackRed      : 0
% 1.97/1.29  
% 1.97/1.29  #Partial instantiations: 0
% 1.97/1.29  #Strategies tried      : 1
% 1.97/1.29  
% 1.97/1.29  Timing (in seconds)
% 1.97/1.29  ----------------------
% 1.97/1.29  Preprocessing        : 0.28
% 1.97/1.29  Parsing              : 0.15
% 1.97/1.29  CNF conversion       : 0.02
% 1.97/1.29  Main loop            : 0.19
% 1.97/1.29  Inferencing          : 0.07
% 1.97/1.29  Reduction            : 0.06
% 1.97/1.29  Demodulation         : 0.04
% 1.97/1.29  BG Simplification    : 0.01
% 1.97/1.29  Subsumption          : 0.04
% 1.97/1.29  Abstraction          : 0.01
% 1.97/1.29  MUC search           : 0.00
% 1.97/1.29  Cooper               : 0.00
% 1.97/1.29  Total                : 0.50
% 1.97/1.29  Index Insertion      : 0.00
% 1.97/1.29  Index Deletion       : 0.00
% 1.97/1.29  Index Matching       : 0.00
% 1.97/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
