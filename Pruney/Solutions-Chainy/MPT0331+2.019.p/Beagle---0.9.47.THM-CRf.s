%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:47 EST 2020

% Result     : Theorem 20.50s
% Output     : CNFRefutation 20.50s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(c_46,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_870,plain,(
    ! [A_101,C_102,B_103] :
      ( r1_xboole_0(k2_tarski(A_101,C_102),B_103)
      | r2_hidden(C_102,B_103)
      | r2_hidden(A_101,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6017,plain,(
    ! [B_206,A_207,C_208] :
      ( r1_xboole_0(B_206,k2_tarski(A_207,C_208))
      | r2_hidden(C_208,B_206)
      | r2_hidden(A_207,B_206) ) ),
    inference(resolution,[status(thm)],[c_870,c_4])).

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

tff(c_49726,plain,(
    ! [B_385,A_386,C_387] :
      ( k4_xboole_0(B_385,k2_tarski(A_386,C_387)) = B_385
      | r2_hidden(C_387,B_385)
      | r2_hidden(A_386,B_385) ) ),
    inference(resolution,[status(thm)],[c_6017,c_47])).

tff(c_42,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_49793,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_49726,c_42])).

tff(c_49841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_49793])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:10:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.50/12.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.50/12.73  
% 20.50/12.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.50/12.74  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 20.50/12.74  
% 20.50/12.74  %Foreground sorts:
% 20.50/12.74  
% 20.50/12.74  
% 20.50/12.74  %Background operators:
% 20.50/12.74  
% 20.50/12.74  
% 20.50/12.74  %Foreground operators:
% 20.50/12.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.50/12.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.50/12.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.50/12.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.50/12.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.50/12.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 20.50/12.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 20.50/12.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 20.50/12.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.50/12.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.50/12.74  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 20.50/12.74  tff('#skF_2', type, '#skF_2': $i).
% 20.50/12.74  tff('#skF_3', type, '#skF_3': $i).
% 20.50/12.74  tff('#skF_1', type, '#skF_1': $i).
% 20.50/12.74  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 20.50/12.74  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 20.50/12.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.50/12.74  tff(k3_tarski, type, k3_tarski: $i > $i).
% 20.50/12.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.50/12.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.50/12.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.50/12.74  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 20.50/12.74  
% 20.50/12.74  tff(f_88, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 20.50/12.74  tff(f_77, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 20.50/12.74  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 20.50/12.74  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 20.50/12.74  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 20.50/12.74  tff(c_46, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 20.50/12.74  tff(c_44, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 20.50/12.74  tff(c_870, plain, (![A_101, C_102, B_103]: (r1_xboole_0(k2_tarski(A_101, C_102), B_103) | r2_hidden(C_102, B_103) | r2_hidden(A_101, B_103))), inference(cnfTransformation, [status(thm)], [f_77])).
% 20.50/12.74  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.50/12.74  tff(c_6017, plain, (![B_206, A_207, C_208]: (r1_xboole_0(B_206, k2_tarski(A_207, C_208)) | r2_hidden(C_208, B_206) | r2_hidden(A_207, B_206))), inference(resolution, [status(thm)], [c_870, c_4])).
% 20.50/12.74  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(A_7, B_8), B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.50/12.74  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 20.50/12.74  tff(c_47, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 20.50/12.74  tff(c_49726, plain, (![B_385, A_386, C_387]: (k4_xboole_0(B_385, k2_tarski(A_386, C_387))=B_385 | r2_hidden(C_387, B_385) | r2_hidden(A_386, B_385))), inference(resolution, [status(thm)], [c_6017, c_47])).
% 20.50/12.74  tff(c_42, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_88])).
% 20.50/12.74  tff(c_49793, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_49726, c_42])).
% 20.50/12.74  tff(c_49841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_49793])).
% 20.50/12.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.50/12.74  
% 20.50/12.74  Inference rules
% 20.50/12.74  ----------------------
% 20.50/12.74  #Ref     : 0
% 20.50/12.74  #Sup     : 13135
% 20.50/12.74  #Fact    : 0
% 20.50/12.74  #Define  : 0
% 20.50/12.74  #Split   : 0
% 20.50/12.74  #Chain   : 0
% 20.50/12.74  #Close   : 0
% 20.50/12.74  
% 20.50/12.74  Ordering : KBO
% 20.50/12.74  
% 20.50/12.74  Simplification rules
% 20.50/12.74  ----------------------
% 20.50/12.74  #Subsume      : 1023
% 20.50/12.74  #Demod        : 16883
% 20.50/12.74  #Tautology    : 4081
% 20.50/12.74  #SimpNegUnit  : 1
% 20.50/12.74  #BackRed      : 2
% 20.50/12.74  
% 20.50/12.74  #Partial instantiations: 0
% 20.50/12.74  #Strategies tried      : 1
% 20.50/12.74  
% 20.50/12.74  Timing (in seconds)
% 20.50/12.74  ----------------------
% 20.50/12.75  Preprocessing        : 0.33
% 20.50/12.75  Parsing              : 0.18
% 20.50/12.75  CNF conversion       : 0.02
% 20.50/12.75  Main loop            : 11.65
% 20.50/12.75  Inferencing          : 1.28
% 20.50/12.75  Reduction            : 8.57
% 20.50/12.75  Demodulation         : 8.20
% 20.50/12.75  BG Simplification    : 0.24
% 20.50/12.75  Subsumption          : 1.27
% 20.62/12.75  Abstraction          : 0.38
% 20.62/12.75  MUC search           : 0.00
% 20.62/12.75  Cooper               : 0.00
% 20.62/12.75  Total                : 12.01
% 20.62/12.75  Index Insertion      : 0.00
% 20.62/12.75  Index Deletion       : 0.00
% 20.62/12.75  Index Matching       : 0.00
% 20.62/12.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
