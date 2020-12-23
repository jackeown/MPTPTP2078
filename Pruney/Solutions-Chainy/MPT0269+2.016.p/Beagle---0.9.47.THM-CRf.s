%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:46 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   48 (  54 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 (  56 expanded)
%              Number of equality atoms :   29 (  43 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_28,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_225,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,k1_tarski(B_43)) = A_42
      | r2_hidden(B_43,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_237,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_32])).

tff(c_245,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_237])).

tff(c_463,plain,(
    ! [B_54,A_55] :
      ( k3_xboole_0(B_54,k1_tarski(A_55)) = k1_tarski(A_55)
      | ~ r2_hidden(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_55,plain,(
    ! [A_28,B_29] : r1_tarski(k4_xboole_0(A_28,B_29),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_55])).

tff(c_101,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_101])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_2])).

tff(c_248,plain,(
    ! [A_44,B_45] : k5_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_263,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_248])).

tff(c_277,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_263])).

tff(c_133,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_151,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_133])).

tff(c_293,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_151])).

tff(c_476,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_293])).

tff(c_513,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_476])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:49:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.29  
% 2.16/1.29  %Foreground sorts:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Background operators:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Foreground operators:
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.29  
% 2.16/1.30  tff(f_66, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 2.16/1.30  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.16/1.30  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 2.16/1.30  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.16/1.30  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.16/1.30  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.16/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.16/1.30  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.16/1.30  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.16/1.30  tff(c_28, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.30  tff(c_30, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.30  tff(c_225, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k1_tarski(B_43))=A_42 | r2_hidden(B_43, A_42))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.30  tff(c_32, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.30  tff(c_237, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_225, c_32])).
% 2.16/1.30  tff(c_245, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_30, c_237])).
% 2.16/1.30  tff(c_463, plain, (![B_54, A_55]: (k3_xboole_0(B_54, k1_tarski(A_55))=k1_tarski(A_55) | ~r2_hidden(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.30  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.30  tff(c_55, plain, (![A_28, B_29]: (r1_tarski(k4_xboole_0(A_28, B_29), A_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.30  tff(c_58, plain, (r1_tarski(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_55])).
% 2.16/1.30  tff(c_101, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.30  tff(c_108, plain, (k3_xboole_0(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_101])).
% 2.16/1.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.30  tff(c_113, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_108, c_2])).
% 2.16/1.30  tff(c_248, plain, (![A_44, B_45]: (k5_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.30  tff(c_263, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_113, c_248])).
% 2.16/1.30  tff(c_277, plain, (k4_xboole_0('#skF_1', k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_263])).
% 2.16/1.30  tff(c_133, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.30  tff(c_151, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_133])).
% 2.16/1.30  tff(c_293, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_277, c_151])).
% 2.16/1.30  tff(c_476, plain, (k1_tarski('#skF_2')='#skF_1' | ~r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_463, c_293])).
% 2.16/1.30  tff(c_513, plain, (k1_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_245, c_476])).
% 2.16/1.30  tff(c_515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_513])).
% 2.16/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  Inference rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Ref     : 0
% 2.16/1.30  #Sup     : 131
% 2.16/1.30  #Fact    : 0
% 2.16/1.30  #Define  : 0
% 2.16/1.30  #Split   : 0
% 2.16/1.30  #Chain   : 0
% 2.16/1.30  #Close   : 0
% 2.16/1.30  
% 2.16/1.30  Ordering : KBO
% 2.16/1.30  
% 2.16/1.30  Simplification rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Subsume      : 3
% 2.16/1.30  #Demod        : 52
% 2.16/1.30  #Tautology    : 85
% 2.16/1.30  #SimpNegUnit  : 3
% 2.16/1.30  #BackRed      : 2
% 2.16/1.30  
% 2.16/1.30  #Partial instantiations: 0
% 2.16/1.30  #Strategies tried      : 1
% 2.16/1.30  
% 2.16/1.30  Timing (in seconds)
% 2.16/1.30  ----------------------
% 2.16/1.30  Preprocessing        : 0.30
% 2.16/1.30  Parsing              : 0.16
% 2.16/1.30  CNF conversion       : 0.02
% 2.16/1.30  Main loop            : 0.24
% 2.16/1.30  Inferencing          : 0.10
% 2.16/1.30  Reduction            : 0.09
% 2.16/1.30  Demodulation         : 0.07
% 2.16/1.30  BG Simplification    : 0.01
% 2.16/1.30  Subsumption          : 0.03
% 2.16/1.30  Abstraction          : 0.01
% 2.16/1.30  MUC search           : 0.00
% 2.16/1.30  Cooper               : 0.00
% 2.16/1.30  Total                : 0.57
% 2.16/1.30  Index Insertion      : 0.00
% 2.16/1.30  Index Deletion       : 0.00
% 2.16/1.30  Index Matching       : 0.00
% 2.16/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
