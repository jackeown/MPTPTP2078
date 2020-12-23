%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:46 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   43 (  62 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  76 expanded)
%              Number of equality atoms :   23 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_64,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_49,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_54,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_95,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(k1_tarski(A_32),k1_tarski(B_33))
      | B_33 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_203,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(k1_tarski(A_59),k1_tarski(B_60)) = k1_tarski(A_59)
      | B_60 = A_59 ) ),
    inference(resolution,[status(thm)],[c_95,c_26])).

tff(c_56,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_222,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_56])).

tff(c_232,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_222])).

tff(c_48,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,(
    ! [D_25,B_26] : r2_hidden(D_25,k2_tarski(D_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_72])).

tff(c_255,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_75])).

tff(c_22,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_86,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = A_30
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_86])).

tff(c_140,plain,(
    ! [D_41,B_42,A_43] :
      ( ~ r2_hidden(D_41,B_42)
      | ~ r2_hidden(D_41,k4_xboole_0(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_143,plain,(
    ! [D_41] :
      ( ~ r2_hidden(D_41,k1_xboole_0)
      | ~ r2_hidden(D_41,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_140])).

tff(c_278,plain,(
    ~ r2_hidden('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_255,c_143])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:40:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.28  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.06/1.28  
% 2.06/1.28  %Foreground sorts:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Background operators:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Foreground operators:
% 2.06/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.06/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.06/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.28  
% 2.06/1.29  tff(f_76, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.06/1.29  tff(f_71, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.06/1.29  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.06/1.29  tff(f_64, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.06/1.29  tff(f_62, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.06/1.29  tff(f_49, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.06/1.29  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.06/1.29  tff(c_54, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.06/1.29  tff(c_95, plain, (![A_32, B_33]: (r1_xboole_0(k1_tarski(A_32), k1_tarski(B_33)) | B_33=A_32)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.06/1.29  tff(c_26, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.06/1.29  tff(c_203, plain, (![A_59, B_60]: (k4_xboole_0(k1_tarski(A_59), k1_tarski(B_60))=k1_tarski(A_59) | B_60=A_59)), inference(resolution, [status(thm)], [c_95, c_26])).
% 2.06/1.29  tff(c_56, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.06/1.29  tff(c_222, plain, (k1_tarski('#skF_5')=k1_xboole_0 | '#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_203, c_56])).
% 2.06/1.29  tff(c_232, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_222])).
% 2.06/1.29  tff(c_48, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.29  tff(c_72, plain, (![D_25, B_26]: (r2_hidden(D_25, k2_tarski(D_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.29  tff(c_75, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_72])).
% 2.06/1.29  tff(c_255, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_232, c_75])).
% 2.06/1.29  tff(c_22, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.29  tff(c_86, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=A_30 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.06/1.29  tff(c_90, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_86])).
% 2.06/1.29  tff(c_140, plain, (![D_41, B_42, A_43]: (~r2_hidden(D_41, B_42) | ~r2_hidden(D_41, k4_xboole_0(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.29  tff(c_143, plain, (![D_41]: (~r2_hidden(D_41, k1_xboole_0) | ~r2_hidden(D_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_90, c_140])).
% 2.06/1.29  tff(c_278, plain, (~r2_hidden('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_255, c_143])).
% 2.06/1.29  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_255, c_278])).
% 2.06/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  Inference rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Ref     : 0
% 2.06/1.29  #Sup     : 56
% 2.06/1.29  #Fact    : 0
% 2.06/1.29  #Define  : 0
% 2.06/1.29  #Split   : 0
% 2.06/1.29  #Chain   : 0
% 2.06/1.29  #Close   : 0
% 2.06/1.29  
% 2.06/1.29  Ordering : KBO
% 2.06/1.29  
% 2.06/1.29  Simplification rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Subsume      : 2
% 2.06/1.29  #Demod        : 6
% 2.06/1.29  #Tautology    : 36
% 2.06/1.29  #SimpNegUnit  : 2
% 2.06/1.29  #BackRed      : 1
% 2.06/1.29  
% 2.06/1.29  #Partial instantiations: 0
% 2.06/1.29  #Strategies tried      : 1
% 2.06/1.29  
% 2.06/1.29  Timing (in seconds)
% 2.06/1.29  ----------------------
% 2.06/1.29  Preprocessing        : 0.32
% 2.06/1.29  Parsing              : 0.17
% 2.06/1.29  CNF conversion       : 0.02
% 2.06/1.29  Main loop            : 0.18
% 2.06/1.29  Inferencing          : 0.06
% 2.06/1.29  Reduction            : 0.06
% 2.06/1.29  Demodulation         : 0.04
% 2.06/1.29  BG Simplification    : 0.02
% 2.06/1.29  Subsumption          : 0.03
% 2.06/1.29  Abstraction          : 0.01
% 2.06/1.29  MUC search           : 0.00
% 2.06/1.29  Cooper               : 0.00
% 2.06/1.29  Total                : 0.53
% 2.06/1.29  Index Insertion      : 0.00
% 2.06/1.29  Index Deletion       : 0.00
% 2.06/1.29  Index Matching       : 0.00
% 2.06/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
