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
% DateTime   : Thu Dec  3 09:49:42 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  32 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),k1_tarski(B_11)) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,(
    ! [B_19,C_20] :
      ( k4_xboole_0(k2_tarski(B_19,B_19),C_20) = k1_tarski(B_19)
      | r2_hidden(B_19,C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_99,plain,(
    ! [B_36,C_37] :
      ( k4_xboole_0(k1_tarski(B_36),C_37) = k1_tarski(B_36)
      | r2_hidden(B_36,C_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    ! [C_45,B_46] :
      ( k5_xboole_0(C_45,k1_tarski(B_46)) = k2_xboole_0(C_45,k1_tarski(B_46))
      | r2_hidden(B_46,C_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_4])).

tff(c_34,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_127,plain,
    ( k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4')
    | r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_34])).

tff(c_133,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_127])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_138,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_133,c_6])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:46:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.16  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.70/1.16  
% 1.70/1.16  %Foreground sorts:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Background operators:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Foreground operators:
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.70/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.70/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.70/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.70/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.70/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.70/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.70/1.16  
% 1.70/1.17  tff(f_59, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 1.70/1.17  tff(f_38, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.70/1.17  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.70/1.17  tff(f_53, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 1.70/1.17  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.70/1.17  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.70/1.17  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.70/1.17  tff(c_18, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), k1_tarski(B_11))=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.70/1.17  tff(c_20, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.70/1.17  tff(c_30, plain, (![B_19, C_20]: (k4_xboole_0(k2_tarski(B_19, B_19), C_20)=k1_tarski(B_19) | r2_hidden(B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.70/1.17  tff(c_99, plain, (![B_36, C_37]: (k4_xboole_0(k1_tarski(B_36), C_37)=k1_tarski(B_36) | r2_hidden(B_36, C_37))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30])).
% 1.70/1.17  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.17  tff(c_121, plain, (![C_45, B_46]: (k5_xboole_0(C_45, k1_tarski(B_46))=k2_xboole_0(C_45, k1_tarski(B_46)) | r2_hidden(B_46, C_45))), inference(superposition, [status(thm), theory('equality')], [c_99, c_4])).
% 1.70/1.17  tff(c_34, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.70/1.17  tff(c_127, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4') | r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_34])).
% 1.70/1.17  tff(c_133, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_127])).
% 1.70/1.17  tff(c_6, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.70/1.17  tff(c_138, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_133, c_6])).
% 1.70/1.17  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_138])).
% 1.70/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  Inference rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Ref     : 0
% 1.70/1.17  #Sup     : 22
% 1.70/1.17  #Fact    : 0
% 1.70/1.17  #Define  : 0
% 1.70/1.17  #Split   : 0
% 1.70/1.17  #Chain   : 0
% 1.70/1.17  #Close   : 0
% 1.70/1.17  
% 1.70/1.17  Ordering : KBO
% 1.70/1.17  
% 1.70/1.17  Simplification rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Subsume      : 0
% 1.70/1.17  #Demod        : 2
% 1.70/1.17  #Tautology    : 18
% 1.70/1.17  #SimpNegUnit  : 1
% 1.70/1.17  #BackRed      : 0
% 1.70/1.17  
% 1.70/1.17  #Partial instantiations: 0
% 1.70/1.17  #Strategies tried      : 1
% 1.70/1.17  
% 1.70/1.17  Timing (in seconds)
% 1.70/1.17  ----------------------
% 1.70/1.17  Preprocessing        : 0.30
% 1.70/1.17  Parsing              : 0.16
% 1.70/1.17  CNF conversion       : 0.02
% 1.70/1.17  Main loop            : 0.12
% 1.70/1.17  Inferencing          : 0.04
% 1.70/1.17  Reduction            : 0.04
% 1.70/1.17  Demodulation         : 0.03
% 1.70/1.17  BG Simplification    : 0.01
% 1.70/1.17  Subsumption          : 0.02
% 1.70/1.17  Abstraction          : 0.01
% 1.70/1.17  MUC search           : 0.00
% 1.70/1.17  Cooper               : 0.00
% 1.70/1.17  Total                : 0.44
% 1.70/1.17  Index Insertion      : 0.00
% 1.70/1.17  Index Deletion       : 0.00
% 1.70/1.17  Index Matching       : 0.00
% 1.70/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
