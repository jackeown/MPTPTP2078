%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:51 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_72,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_74,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [B_22] : r1_tarski(B_22,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_257,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_261,plain,(
    ! [B_22] : k3_xboole_0(B_22,B_22) = B_22 ),
    inference(resolution,[status(thm)],[c_48,c_257])).

tff(c_271,plain,(
    ! [A_62,B_63,C_64] : r1_tarski(k3_xboole_0(A_62,B_63),k2_xboole_0(A_62,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_319,plain,(
    ! [B_67,C_68] : r1_tarski(B_67,k2_xboole_0(B_67,C_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_271])).

tff(c_502,plain,(
    ! [B_78,A_79] : r1_tarski(B_78,k2_xboole_0(A_79,B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_319])).

tff(c_508,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_502])).

tff(c_70,plain,(
    ! [B_47,A_46] :
      ( B_47 = A_46
      | ~ r1_tarski(k1_tarski(A_46),k1_tarski(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_533,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_508,c_70])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_533])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.28  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.19/1.28  
% 2.19/1.28  %Foreground sorts:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Background operators:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Foreground operators:
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.28  
% 2.19/1.29  tff(f_92, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.19/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.19/1.29  tff(f_61, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.19/1.29  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.19/1.29  tff(f_71, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 2.19/1.29  tff(f_87, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.19/1.29  tff(c_72, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.19/1.29  tff(c_74, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.19/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.29  tff(c_48, plain, (![B_22]: (r1_tarski(B_22, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.19/1.29  tff(c_257, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.19/1.29  tff(c_261, plain, (![B_22]: (k3_xboole_0(B_22, B_22)=B_22)), inference(resolution, [status(thm)], [c_48, c_257])).
% 2.19/1.29  tff(c_271, plain, (![A_62, B_63, C_64]: (r1_tarski(k3_xboole_0(A_62, B_63), k2_xboole_0(A_62, C_64)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.29  tff(c_319, plain, (![B_67, C_68]: (r1_tarski(B_67, k2_xboole_0(B_67, C_68)))), inference(superposition, [status(thm), theory('equality')], [c_261, c_271])).
% 2.19/1.29  tff(c_502, plain, (![B_78, A_79]: (r1_tarski(B_78, k2_xboole_0(A_79, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_319])).
% 2.19/1.29  tff(c_508, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_502])).
% 2.19/1.29  tff(c_70, plain, (![B_47, A_46]: (B_47=A_46 | ~r1_tarski(k1_tarski(A_46), k1_tarski(B_47)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.19/1.29  tff(c_533, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_508, c_70])).
% 2.19/1.29  tff(c_540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_533])).
% 2.19/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  Inference rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Ref     : 0
% 2.19/1.29  #Sup     : 112
% 2.19/1.29  #Fact    : 0
% 2.19/1.29  #Define  : 0
% 2.19/1.29  #Split   : 0
% 2.19/1.29  #Chain   : 0
% 2.19/1.29  #Close   : 0
% 2.19/1.29  
% 2.19/1.29  Ordering : KBO
% 2.19/1.29  
% 2.19/1.29  Simplification rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Subsume      : 0
% 2.19/1.29  #Demod        : 40
% 2.19/1.29  #Tautology    : 89
% 2.19/1.29  #SimpNegUnit  : 1
% 2.19/1.29  #BackRed      : 0
% 2.19/1.29  
% 2.19/1.29  #Partial instantiations: 0
% 2.19/1.29  #Strategies tried      : 1
% 2.19/1.29  
% 2.19/1.29  Timing (in seconds)
% 2.19/1.29  ----------------------
% 2.19/1.29  Preprocessing        : 0.34
% 2.19/1.29  Parsing              : 0.18
% 2.19/1.29  CNF conversion       : 0.02
% 2.19/1.29  Main loop            : 0.21
% 2.19/1.29  Inferencing          : 0.06
% 2.19/1.29  Reduction            : 0.08
% 2.19/1.29  Demodulation         : 0.06
% 2.19/1.29  BG Simplification    : 0.02
% 2.19/1.29  Subsumption          : 0.04
% 2.19/1.29  Abstraction          : 0.01
% 2.19/1.29  MUC search           : 0.00
% 2.19/1.29  Cooper               : 0.00
% 2.19/1.29  Total                : 0.57
% 2.19/1.29  Index Insertion      : 0.00
% 2.19/1.29  Index Deletion       : 0.00
% 2.19/1.29  Index Matching       : 0.00
% 2.19/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
