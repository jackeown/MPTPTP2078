%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:57 EST 2020

% Result     : Theorem 14.71s
% Output     : CNFRefutation 14.82s
% Verified   : 
% Statistics : Number of formulae       :   45 (  54 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  54 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    k3_xboole_0('#skF_2','#skF_4') != k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_51,plain,(
    k3_xboole_0('#skF_4','#skF_2') != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_628,plain,(
    ! [A_71,B_72] :
      ( k2_xboole_0(k1_tarski(A_71),B_72) = B_72
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5363,plain,(
    ! [A_175,B_176] :
      ( k3_xboole_0(k1_tarski(A_175),B_176) = k1_tarski(A_175)
      | ~ r2_hidden(A_175,B_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_16])).

tff(c_46219,plain,(
    ! [B_498,A_499] :
      ( k3_xboole_0(B_498,k1_tarski(A_499)) = k1_tarski(A_499)
      | ~ r2_hidden(A_499,B_498) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5363])).

tff(c_48,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_50,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_170,plain,(
    ! [A_53,B_54] :
      ( k2_xboole_0(A_53,B_54) = B_54
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_194,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_170])).

tff(c_1750,plain,(
    ! [A_110,B_111,C_112] : k3_xboole_0(k3_xboole_0(A_110,B_111),C_112) = k3_xboole_0(A_110,k3_xboole_0(B_111,C_112)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13287,plain,(
    ! [A_267,B_268,C_269] : k3_xboole_0(A_267,k3_xboole_0(k2_xboole_0(A_267,B_268),C_269)) = k3_xboole_0(A_267,C_269) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1750])).

tff(c_14227,plain,(
    ! [C_278] : k3_xboole_0('#skF_2',k3_xboole_0('#skF_3',C_278)) = k3_xboole_0('#skF_2',C_278) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_13287])).

tff(c_14436,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_5')) = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_14227])).

tff(c_14486,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_5')) = k3_xboole_0('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14436])).

tff(c_46450,plain,
    ( k3_xboole_0('#skF_4','#skF_2') = k1_tarski('#skF_5')
    | ~ r2_hidden('#skF_5','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_46219,c_14486])).

tff(c_46794,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46450])).

tff(c_46796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_46794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:17:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.71/7.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.71/7.24  
% 14.71/7.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.71/7.24  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 14.71/7.24  
% 14.71/7.24  %Foreground sorts:
% 14.71/7.24  
% 14.71/7.24  
% 14.71/7.24  %Background operators:
% 14.71/7.24  
% 14.71/7.24  
% 14.71/7.24  %Foreground operators:
% 14.71/7.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.71/7.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.71/7.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.71/7.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.71/7.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.71/7.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.71/7.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.71/7.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.71/7.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.71/7.24  tff('#skF_5', type, '#skF_5': $i).
% 14.71/7.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.71/7.24  tff('#skF_2', type, '#skF_2': $i).
% 14.71/7.24  tff('#skF_3', type, '#skF_3': $i).
% 14.71/7.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.71/7.24  tff('#skF_4', type, '#skF_4': $i).
% 14.71/7.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.71/7.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.71/7.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.71/7.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.71/7.24  
% 14.82/7.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.82/7.25  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 14.82/7.25  tff(f_68, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 14.82/7.25  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 14.82/7.25  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 14.82/7.25  tff(f_40, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 14.82/7.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.82/7.25  tff(c_44, plain, (k3_xboole_0('#skF_2', '#skF_4')!=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.82/7.25  tff(c_51, plain, (k3_xboole_0('#skF_4', '#skF_2')!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 14.82/7.25  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.82/7.25  tff(c_628, plain, (![A_71, B_72]: (k2_xboole_0(k1_tarski(A_71), B_72)=B_72 | ~r2_hidden(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.82/7.25  tff(c_16, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.82/7.25  tff(c_5363, plain, (![A_175, B_176]: (k3_xboole_0(k1_tarski(A_175), B_176)=k1_tarski(A_175) | ~r2_hidden(A_175, B_176))), inference(superposition, [status(thm), theory('equality')], [c_628, c_16])).
% 14.82/7.25  tff(c_46219, plain, (![B_498, A_499]: (k3_xboole_0(B_498, k1_tarski(A_499))=k1_tarski(A_499) | ~r2_hidden(A_499, B_498))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5363])).
% 14.82/7.25  tff(c_48, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.82/7.25  tff(c_50, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.82/7.25  tff(c_170, plain, (![A_53, B_54]: (k2_xboole_0(A_53, B_54)=B_54 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.82/7.25  tff(c_194, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_50, c_170])).
% 14.82/7.25  tff(c_1750, plain, (![A_110, B_111, C_112]: (k3_xboole_0(k3_xboole_0(A_110, B_111), C_112)=k3_xboole_0(A_110, k3_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.82/7.25  tff(c_13287, plain, (![A_267, B_268, C_269]: (k3_xboole_0(A_267, k3_xboole_0(k2_xboole_0(A_267, B_268), C_269))=k3_xboole_0(A_267, C_269))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1750])).
% 14.82/7.25  tff(c_14227, plain, (![C_278]: (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', C_278))=k3_xboole_0('#skF_2', C_278))), inference(superposition, [status(thm), theory('equality')], [c_194, c_13287])).
% 14.82/7.25  tff(c_14436, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_5'))=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_14227])).
% 14.82/7.25  tff(c_14486, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_5'))=k3_xboole_0('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14436])).
% 14.82/7.25  tff(c_46450, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_tarski('#skF_5') | ~r2_hidden('#skF_5', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46219, c_14486])).
% 14.82/7.25  tff(c_46794, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46450])).
% 14.82/7.25  tff(c_46796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_46794])).
% 14.82/7.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.82/7.25  
% 14.82/7.25  Inference rules
% 14.82/7.25  ----------------------
% 14.82/7.25  #Ref     : 0
% 14.82/7.25  #Sup     : 11516
% 14.82/7.25  #Fact    : 4
% 14.82/7.25  #Define  : 0
% 14.82/7.25  #Split   : 2
% 14.82/7.25  #Chain   : 0
% 14.82/7.25  #Close   : 0
% 14.82/7.25  
% 14.82/7.25  Ordering : KBO
% 14.82/7.25  
% 14.82/7.25  Simplification rules
% 14.82/7.25  ----------------------
% 14.82/7.25  #Subsume      : 274
% 14.82/7.25  #Demod        : 12108
% 14.82/7.25  #Tautology    : 7329
% 14.82/7.25  #SimpNegUnit  : 26
% 14.82/7.25  #BackRed      : 12
% 14.82/7.25  
% 14.82/7.25  #Partial instantiations: 0
% 14.82/7.25  #Strategies tried      : 1
% 14.82/7.25  
% 14.82/7.25  Timing (in seconds)
% 14.82/7.25  ----------------------
% 14.82/7.25  Preprocessing        : 0.33
% 14.82/7.25  Parsing              : 0.18
% 14.82/7.25  CNF conversion       : 0.02
% 14.82/7.25  Main loop            : 6.10
% 14.82/7.25  Inferencing          : 0.87
% 14.82/7.25  Reduction            : 3.81
% 14.82/7.25  Demodulation         : 3.44
% 14.82/7.25  BG Simplification    : 0.12
% 14.82/7.25  Subsumption          : 1.03
% 14.82/7.25  Abstraction          : 0.16
% 14.82/7.26  MUC search           : 0.00
% 14.82/7.26  Cooper               : 0.00
% 14.82/7.26  Total                : 6.45
% 14.82/7.26  Index Insertion      : 0.00
% 14.82/7.26  Index Deletion       : 0.00
% 14.82/7.26  Index Matching       : 0.00
% 14.82/7.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
