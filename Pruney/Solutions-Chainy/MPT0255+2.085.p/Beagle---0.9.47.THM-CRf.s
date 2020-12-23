%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:50 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 156 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :   44 ( 180 expanded)
%              Number of equality atoms :   11 (  82 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
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
    k2_xboole_0(k2_tarski('#skF_2','#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    r1_tarski(k2_tarski('#skF_2','#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_18])).

tff(c_14,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_104,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_14])).

tff(c_50,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    k2_xboole_0('#skF_4',k2_tarski('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_50])).

tff(c_132,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_92])).

tff(c_136,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_18])).

tff(c_143,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_136,c_14])).

tff(c_12,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_149,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_12])).

tff(c_147,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_104])).

tff(c_514,plain,(
    ! [B_61,C_62,A_63] :
      ( r2_hidden(B_61,C_62)
      | ~ r1_tarski(k2_tarski(A_63,B_61),C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_525,plain,(
    ! [C_62] :
      ( r2_hidden('#skF_3',C_62)
      | ~ r1_tarski('#skF_4',C_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_514])).

tff(c_533,plain,(
    ! [C_62] : r2_hidden('#skF_3',C_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_525])).

tff(c_16,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_150,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_16])).

tff(c_991,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | ~ r2_hidden(C_88,B_87)
      | ~ r2_hidden(C_88,A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_995,plain,(
    ! [C_89,A_90] :
      ( ~ r2_hidden(C_89,'#skF_4')
      | ~ r2_hidden(C_89,A_90) ) ),
    inference(resolution,[status(thm)],[c_150,c_991])).

tff(c_1001,plain,(
    ! [A_90] : ~ r2_hidden('#skF_3',A_90) ),
    inference(resolution,[status(thm)],[c_533,c_995])).

tff(c_1013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_1001])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.37  
% 2.52/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.52/1.38  
% 2.52/1.38  %Foreground sorts:
% 2.52/1.38  
% 2.52/1.38  
% 2.52/1.38  %Background operators:
% 2.52/1.38  
% 2.52/1.38  
% 2.52/1.38  %Foreground operators:
% 2.52/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.52/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.52/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.52/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.52/1.38  
% 2.52/1.39  tff(f_75, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.52/1.39  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.52/1.39  tff(f_55, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.52/1.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.52/1.39  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.52/1.39  tff(f_71, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.52/1.39  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.52/1.39  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.52/1.39  tff(c_32, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.52/1.39  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.52/1.39  tff(c_46, plain, (r1_tarski(k2_tarski('#skF_2', '#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_18])).
% 2.52/1.39  tff(c_14, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.39  tff(c_104, plain, (k2_tarski('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_14])).
% 2.52/1.39  tff(c_50, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.52/1.39  tff(c_92, plain, (k2_xboole_0('#skF_4', k2_tarski('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_32, c_50])).
% 2.52/1.39  tff(c_132, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_92])).
% 2.52/1.39  tff(c_136, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_132, c_18])).
% 2.52/1.39  tff(c_143, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_136, c_14])).
% 2.52/1.39  tff(c_12, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.52/1.39  tff(c_149, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_12])).
% 2.52/1.39  tff(c_147, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_104])).
% 2.52/1.39  tff(c_514, plain, (![B_61, C_62, A_63]: (r2_hidden(B_61, C_62) | ~r1_tarski(k2_tarski(A_63, B_61), C_62))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.52/1.39  tff(c_525, plain, (![C_62]: (r2_hidden('#skF_3', C_62) | ~r1_tarski('#skF_4', C_62))), inference(superposition, [status(thm), theory('equality')], [c_147, c_514])).
% 2.52/1.39  tff(c_533, plain, (![C_62]: (r2_hidden('#skF_3', C_62))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_525])).
% 2.52/1.39  tff(c_16, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.52/1.39  tff(c_150, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_16])).
% 2.52/1.39  tff(c_991, plain, (![A_86, B_87, C_88]: (~r1_xboole_0(A_86, B_87) | ~r2_hidden(C_88, B_87) | ~r2_hidden(C_88, A_86))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.52/1.39  tff(c_995, plain, (![C_89, A_90]: (~r2_hidden(C_89, '#skF_4') | ~r2_hidden(C_89, A_90))), inference(resolution, [status(thm)], [c_150, c_991])).
% 2.52/1.39  tff(c_1001, plain, (![A_90]: (~r2_hidden('#skF_3', A_90))), inference(resolution, [status(thm)], [c_533, c_995])).
% 2.52/1.39  tff(c_1013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_533, c_1001])).
% 2.52/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.39  
% 2.52/1.39  Inference rules
% 2.52/1.39  ----------------------
% 2.52/1.39  #Ref     : 0
% 2.52/1.39  #Sup     : 234
% 2.52/1.39  #Fact    : 0
% 2.52/1.39  #Define  : 0
% 2.52/1.39  #Split   : 0
% 2.52/1.39  #Chain   : 0
% 2.52/1.39  #Close   : 0
% 2.52/1.39  
% 2.52/1.39  Ordering : KBO
% 2.52/1.39  
% 2.52/1.39  Simplification rules
% 2.52/1.39  ----------------------
% 2.52/1.39  #Subsume      : 3
% 2.52/1.39  #Demod        : 247
% 2.52/1.39  #Tautology    : 197
% 2.52/1.39  #SimpNegUnit  : 0
% 2.52/1.39  #BackRed      : 10
% 2.52/1.39  
% 2.52/1.39  #Partial instantiations: 0
% 2.52/1.39  #Strategies tried      : 1
% 2.52/1.39  
% 2.52/1.39  Timing (in seconds)
% 2.52/1.39  ----------------------
% 2.52/1.39  Preprocessing        : 0.29
% 2.52/1.39  Parsing              : 0.16
% 2.52/1.39  CNF conversion       : 0.02
% 2.52/1.39  Main loop            : 0.33
% 2.52/1.39  Inferencing          : 0.12
% 2.52/1.39  Reduction            : 0.13
% 2.52/1.39  Demodulation         : 0.11
% 2.52/1.39  BG Simplification    : 0.01
% 2.52/1.39  Subsumption          : 0.05
% 2.52/1.39  Abstraction          : 0.02
% 2.52/1.39  MUC search           : 0.00
% 2.52/1.39  Cooper               : 0.00
% 2.52/1.39  Total                : 0.65
% 2.52/1.39  Index Insertion      : 0.00
% 2.52/1.39  Index Deletion       : 0.00
% 2.52/1.39  Index Matching       : 0.00
% 2.75/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
