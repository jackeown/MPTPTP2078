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
% DateTime   : Thu Dec  3 10:00:08 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k2_relat_1(B))
         => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(c_36,plain,(
    k2_relat_1(k8_relat_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski('#skF_1'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(B_4,C_5) = A_3
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_161,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_tarski('#skF_1'(A_78,B_79,C_80),A_78)
      | k3_xboole_0(B_79,C_80) = A_78
      | ~ r1_tarski(A_78,C_80)
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_165,plain,(
    ! [B_4,C_5] :
      ( k3_xboole_0(B_4,C_5) = C_5
      | ~ r1_tarski(C_5,C_5)
      | ~ r1_tarski(C_5,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_161])).

tff(c_176,plain,(
    ! [B_81,C_82] :
      ( k3_xboole_0(B_81,C_82) = C_82
      | ~ r1_tarski(C_82,B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_165])).

tff(c_191,plain,(
    k3_xboole_0(k2_relat_1('#skF_3'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_176])).

tff(c_30,plain,(
    ! [B_38,A_37] :
      ( k3_xboole_0(k2_relat_1(B_38),A_37) = k2_relat_1(k8_relat_1(A_37,B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_213,plain,
    ( k2_relat_1(k8_relat_1('#skF_2','#skF_3')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_30])).

tff(c_220,plain,(
    k2_relat_1(k8_relat_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_213])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:55:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.21  
% 2.07/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.21  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 2.07/1.21  
% 2.07/1.21  %Foreground sorts:
% 2.07/1.21  
% 2.07/1.21  
% 2.07/1.21  %Background operators:
% 2.07/1.21  
% 2.07/1.21  
% 2.07/1.21  %Foreground operators:
% 2.07/1.21  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.07/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.07/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.07/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.07/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.07/1.21  
% 2.07/1.22  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 2.07/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.07/1.22  tff(f_44, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 2.07/1.22  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 2.07/1.22  tff(c_36, plain, (k2_relat_1(k8_relat_1('#skF_2', '#skF_3'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.07/1.22  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.07/1.22  tff(c_38, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.07/1.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.22  tff(c_10, plain, (![A_3, B_4, C_5]: (r1_tarski('#skF_1'(A_3, B_4, C_5), C_5) | k3_xboole_0(B_4, C_5)=A_3 | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.22  tff(c_161, plain, (![A_78, B_79, C_80]: (~r1_tarski('#skF_1'(A_78, B_79, C_80), A_78) | k3_xboole_0(B_79, C_80)=A_78 | ~r1_tarski(A_78, C_80) | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.22  tff(c_165, plain, (![B_4, C_5]: (k3_xboole_0(B_4, C_5)=C_5 | ~r1_tarski(C_5, C_5) | ~r1_tarski(C_5, B_4))), inference(resolution, [status(thm)], [c_10, c_161])).
% 2.07/1.22  tff(c_176, plain, (![B_81, C_82]: (k3_xboole_0(B_81, C_82)=C_82 | ~r1_tarski(C_82, B_81))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_165])).
% 2.07/1.22  tff(c_191, plain, (k3_xboole_0(k2_relat_1('#skF_3'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_38, c_176])).
% 2.07/1.22  tff(c_30, plain, (![B_38, A_37]: (k3_xboole_0(k2_relat_1(B_38), A_37)=k2_relat_1(k8_relat_1(A_37, B_38)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.07/1.22  tff(c_213, plain, (k2_relat_1(k8_relat_1('#skF_2', '#skF_3'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_191, c_30])).
% 2.07/1.22  tff(c_220, plain, (k2_relat_1(k8_relat_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_213])).
% 2.07/1.22  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_220])).
% 2.07/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.22  
% 2.07/1.22  Inference rules
% 2.07/1.22  ----------------------
% 2.07/1.22  #Ref     : 0
% 2.07/1.22  #Sup     : 40
% 2.07/1.22  #Fact    : 0
% 2.07/1.22  #Define  : 0
% 2.07/1.22  #Split   : 1
% 2.07/1.22  #Chain   : 0
% 2.07/1.22  #Close   : 0
% 2.07/1.22  
% 2.07/1.22  Ordering : KBO
% 2.07/1.22  
% 2.07/1.22  Simplification rules
% 2.07/1.22  ----------------------
% 2.07/1.22  #Subsume      : 0
% 2.07/1.22  #Demod        : 6
% 2.07/1.22  #Tautology    : 25
% 2.07/1.22  #SimpNegUnit  : 1
% 2.07/1.22  #BackRed      : 0
% 2.07/1.22  
% 2.07/1.22  #Partial instantiations: 0
% 2.07/1.22  #Strategies tried      : 1
% 2.07/1.22  
% 2.07/1.22  Timing (in seconds)
% 2.07/1.22  ----------------------
% 2.07/1.23  Preprocessing        : 0.31
% 2.07/1.23  Parsing              : 0.17
% 2.07/1.23  CNF conversion       : 0.02
% 2.07/1.23  Main loop            : 0.16
% 2.07/1.23  Inferencing          : 0.06
% 2.07/1.23  Reduction            : 0.05
% 2.07/1.23  Demodulation         : 0.03
% 2.07/1.23  BG Simplification    : 0.01
% 2.07/1.23  Subsumption          : 0.03
% 2.07/1.23  Abstraction          : 0.01
% 2.07/1.23  MUC search           : 0.00
% 2.07/1.23  Cooper               : 0.00
% 2.07/1.23  Total                : 0.49
% 2.07/1.23  Index Insertion      : 0.00
% 2.07/1.23  Index Deletion       : 0.00
% 2.07/1.23  Index Matching       : 0.00
% 2.07/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
