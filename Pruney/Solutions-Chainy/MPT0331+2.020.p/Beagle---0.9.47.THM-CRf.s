%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:47 EST 2020

% Result     : Theorem 24.73s
% Output     : CNFRefutation 24.83s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  39 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(c_46,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_858,plain,(
    ! [A_97,C_98,B_99] :
      ( r1_xboole_0(k2_tarski(A_97,C_98),B_99)
      | r2_hidden(C_98,B_99)
      | r2_hidden(A_97,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5969,plain,(
    ! [B_207,A_208,C_209] :
      ( r1_xboole_0(B_207,k2_tarski(A_208,C_209))
      | r2_hidden(C_209,B_207)
      | r2_hidden(A_208,B_207) ) ),
    inference(resolution,[status(thm)],[c_858,c_4])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(k2_xboole_0(A_7,B_8),B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k2_xboole_0(A_13,B_14),B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_60768,plain,(
    ! [B_406,A_407,C_408] :
      ( k4_xboole_0(B_406,k2_tarski(A_407,C_408)) = B_406
      | r2_hidden(C_408,B_406)
      | r2_hidden(A_407,B_406) ) ),
    inference(resolution,[status(thm)],[c_5969,c_47])).

tff(c_42,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_60840,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_60768,c_42])).

tff(c_60895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_60840])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:40:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.73/16.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.73/16.73  
% 24.73/16.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.73/16.73  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 24.73/16.73  
% 24.73/16.73  %Foreground sorts:
% 24.73/16.73  
% 24.73/16.73  
% 24.73/16.73  %Background operators:
% 24.73/16.73  
% 24.73/16.73  
% 24.73/16.73  %Foreground operators:
% 24.73/16.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.73/16.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.73/16.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 24.73/16.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 24.73/16.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.73/16.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 24.73/16.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 24.73/16.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 24.73/16.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.73/16.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 24.73/16.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 24.73/16.73  tff('#skF_2', type, '#skF_2': $i).
% 24.73/16.73  tff('#skF_3', type, '#skF_3': $i).
% 24.73/16.73  tff('#skF_1', type, '#skF_1': $i).
% 24.73/16.73  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 24.73/16.73  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 24.73/16.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.73/16.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 24.73/16.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.73/16.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.73/16.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.73/16.73  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 24.73/16.73  
% 24.83/16.74  tff(f_88, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 24.83/16.74  tff(f_75, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 24.83/16.74  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 24.83/16.74  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 24.83/16.74  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 24.83/16.74  tff(c_46, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 24.83/16.74  tff(c_44, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 24.83/16.74  tff(c_858, plain, (![A_97, C_98, B_99]: (r1_xboole_0(k2_tarski(A_97, C_98), B_99) | r2_hidden(C_98, B_99) | r2_hidden(A_97, B_99))), inference(cnfTransformation, [status(thm)], [f_75])).
% 24.83/16.74  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.83/16.74  tff(c_5969, plain, (![B_207, A_208, C_209]: (r1_xboole_0(B_207, k2_tarski(A_208, C_209)) | r2_hidden(C_209, B_207) | r2_hidden(A_208, B_207))), inference(resolution, [status(thm)], [c_858, c_4])).
% 24.83/16.74  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(A_7, B_8), B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.83/16.74  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 24.83/16.74  tff(c_47, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 24.83/16.74  tff(c_60768, plain, (![B_406, A_407, C_408]: (k4_xboole_0(B_406, k2_tarski(A_407, C_408))=B_406 | r2_hidden(C_408, B_406) | r2_hidden(A_407, B_406))), inference(resolution, [status(thm)], [c_5969, c_47])).
% 24.83/16.74  tff(c_42, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_88])).
% 24.83/16.74  tff(c_60840, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_60768, c_42])).
% 24.83/16.74  tff(c_60895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_60840])).
% 24.83/16.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.83/16.74  
% 24.83/16.74  Inference rules
% 24.83/16.74  ----------------------
% 24.83/16.74  #Ref     : 0
% 24.83/16.74  #Sup     : 16059
% 24.83/16.74  #Fact    : 0
% 24.83/16.74  #Define  : 0
% 24.83/16.74  #Split   : 0
% 24.83/16.74  #Chain   : 0
% 24.83/16.74  #Close   : 0
% 24.83/16.74  
% 24.83/16.74  Ordering : KBO
% 24.83/16.74  
% 24.83/16.74  Simplification rules
% 24.83/16.74  ----------------------
% 24.83/16.74  #Subsume      : 975
% 24.83/16.74  #Demod        : 23886
% 24.83/16.74  #Tautology    : 5456
% 24.83/16.74  #SimpNegUnit  : 1
% 24.83/16.74  #BackRed      : 2
% 24.83/16.74  
% 24.83/16.74  #Partial instantiations: 0
% 24.83/16.74  #Strategies tried      : 1
% 24.83/16.74  
% 24.83/16.74  Timing (in seconds)
% 24.83/16.74  ----------------------
% 24.83/16.74  Preprocessing        : 0.32
% 24.83/16.74  Parsing              : 0.17
% 24.83/16.74  CNF conversion       : 0.02
% 24.83/16.74  Main loop            : 15.68
% 24.83/16.74  Inferencing          : 1.54
% 24.83/16.74  Reduction            : 11.74
% 24.83/16.74  Demodulation         : 11.29
% 24.83/16.74  BG Simplification    : 0.30
% 24.83/16.74  Subsumption          : 1.72
% 24.83/16.74  Abstraction          : 0.47
% 24.83/16.74  MUC search           : 0.00
% 24.83/16.74  Cooper               : 0.00
% 24.83/16.74  Total                : 16.02
% 24.83/16.74  Index Insertion      : 0.00
% 24.83/16.74  Index Deletion       : 0.00
% 24.83/16.75  Index Matching       : 0.00
% 24.83/16.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
