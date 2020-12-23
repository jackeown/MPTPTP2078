%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:28 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  31 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v4_relat_1(B,A) )
       => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_8,plain,(
    k7_relat_1('#skF_2','#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_19,plain,(
    ! [B_9,A_10] :
      ( k7_relat_1(B_9,A_10) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_10)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [B_11,A_12] :
      ( k7_relat_1(B_11,A_12) = B_11
      | ~ v4_relat_1(B_11,A_12)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_4,c_19])).

tff(c_27,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_24])).

tff(c_30,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_27])).

tff(c_32,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:58:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.16  
% 1.62/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.16  %$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.62/1.16  
% 1.62/1.16  %Foreground sorts:
% 1.62/1.16  
% 1.62/1.16  
% 1.62/1.16  %Background operators:
% 1.62/1.16  
% 1.62/1.16  
% 1.62/1.16  %Foreground operators:
% 1.62/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.62/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.62/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.16  
% 1.69/1.17  tff(f_44, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.69/1.17  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.69/1.17  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.69/1.17  tff(c_8, plain, (k7_relat_1('#skF_2', '#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.69/1.17  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.69/1.17  tff(c_10, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.69/1.17  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.17  tff(c_19, plain, (![B_9, A_10]: (k7_relat_1(B_9, A_10)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_10) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.69/1.17  tff(c_24, plain, (![B_11, A_12]: (k7_relat_1(B_11, A_12)=B_11 | ~v4_relat_1(B_11, A_12) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_4, c_19])).
% 1.69/1.17  tff(c_27, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_24])).
% 1.69/1.17  tff(c_30, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_27])).
% 1.69/1.17  tff(c_32, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_30])).
% 1.69/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  Inference rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Ref     : 0
% 1.69/1.17  #Sup     : 3
% 1.69/1.17  #Fact    : 0
% 1.69/1.17  #Define  : 0
% 1.69/1.17  #Split   : 0
% 1.69/1.17  #Chain   : 0
% 1.69/1.17  #Close   : 0
% 1.69/1.17  
% 1.69/1.17  Ordering : KBO
% 1.69/1.17  
% 1.69/1.17  Simplification rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Subsume      : 0
% 1.69/1.17  #Demod        : 1
% 1.69/1.17  #Tautology    : 1
% 1.69/1.17  #SimpNegUnit  : 1
% 1.69/1.17  #BackRed      : 0
% 1.69/1.17  
% 1.69/1.17  #Partial instantiations: 0
% 1.69/1.17  #Strategies tried      : 1
% 1.69/1.17  
% 1.69/1.17  Timing (in seconds)
% 1.69/1.17  ----------------------
% 1.69/1.17  Preprocessing        : 0.27
% 1.69/1.17  Parsing              : 0.15
% 1.69/1.17  CNF conversion       : 0.02
% 1.69/1.17  Main loop            : 0.08
% 1.69/1.17  Inferencing          : 0.04
% 1.69/1.17  Reduction            : 0.02
% 1.69/1.17  Demodulation         : 0.01
% 1.69/1.17  BG Simplification    : 0.01
% 1.69/1.17  Subsumption          : 0.01
% 1.69/1.17  Abstraction          : 0.00
% 1.69/1.17  MUC search           : 0.00
% 1.69/1.17  Cooper               : 0.00
% 1.69/1.17  Total                : 0.37
% 1.69/1.17  Index Insertion      : 0.00
% 1.69/1.17  Index Deletion       : 0.00
% 1.69/1.17  Index Matching       : 0.00
% 1.69/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
