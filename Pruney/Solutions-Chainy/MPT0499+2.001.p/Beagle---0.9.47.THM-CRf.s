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
% DateTime   : Thu Dec  3 09:59:47 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  33 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(k1_relat_1(B),A)
         => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_6,plain,(
    k7_relat_1('#skF_2','#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k5_relat_1(k6_relat_1(A_7),B_8) = B_8
      | ~ r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23,plain,
    ( k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_20])).

tff(c_26,plain,(
    k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_23])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k5_relat_1(k6_relat_1(A_3),B_4) = k7_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_37,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_30])).

tff(c_39,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:01:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.08  
% 1.51/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.08  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.60/1.08  
% 1.60/1.08  %Foreground sorts:
% 1.60/1.08  
% 1.60/1.08  
% 1.60/1.08  %Background operators:
% 1.60/1.08  
% 1.60/1.08  
% 1.60/1.08  %Foreground operators:
% 1.60/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.60/1.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.60/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.60/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.08  
% 1.60/1.09  tff(f_42, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.60/1.09  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 1.60/1.09  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.60/1.09  tff(c_6, plain, (k7_relat_1('#skF_2', '#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.60/1.09  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.60/1.09  tff(c_8, plain, (r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.60/1.09  tff(c_20, plain, (![A_7, B_8]: (k5_relat_1(k6_relat_1(A_7), B_8)=B_8 | ~r1_tarski(k1_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.09  tff(c_23, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_20])).
% 1.60/1.09  tff(c_26, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_23])).
% 1.60/1.09  tff(c_4, plain, (![A_3, B_4]: (k5_relat_1(k6_relat_1(A_3), B_4)=k7_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.60/1.09  tff(c_30, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_4])).
% 1.60/1.09  tff(c_37, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_30])).
% 1.60/1.09  tff(c_39, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_37])).
% 1.60/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.09  
% 1.60/1.09  Inference rules
% 1.60/1.09  ----------------------
% 1.60/1.09  #Ref     : 0
% 1.60/1.09  #Sup     : 7
% 1.60/1.09  #Fact    : 0
% 1.60/1.09  #Define  : 0
% 1.60/1.09  #Split   : 0
% 1.60/1.09  #Chain   : 0
% 1.60/1.09  #Close   : 0
% 1.60/1.09  
% 1.60/1.09  Ordering : KBO
% 1.60/1.09  
% 1.60/1.09  Simplification rules
% 1.60/1.09  ----------------------
% 1.60/1.09  #Subsume      : 0
% 1.60/1.09  #Demod        : 2
% 1.60/1.09  #Tautology    : 3
% 1.60/1.09  #SimpNegUnit  : 1
% 1.60/1.09  #BackRed      : 0
% 1.60/1.09  
% 1.60/1.09  #Partial instantiations: 0
% 1.60/1.09  #Strategies tried      : 1
% 1.60/1.09  
% 1.60/1.09  Timing (in seconds)
% 1.60/1.09  ----------------------
% 1.60/1.09  Preprocessing        : 0.24
% 1.60/1.09  Parsing              : 0.14
% 1.60/1.09  CNF conversion       : 0.01
% 1.60/1.09  Main loop            : 0.07
% 1.60/1.09  Inferencing          : 0.04
% 1.60/1.09  Reduction            : 0.02
% 1.60/1.09  Demodulation         : 0.01
% 1.60/1.09  BG Simplification    : 0.01
% 1.60/1.09  Subsumption          : 0.00
% 1.60/1.09  Abstraction          : 0.00
% 1.60/1.09  MUC search           : 0.00
% 1.60/1.09  Cooper               : 0.00
% 1.60/1.09  Total                : 0.34
% 1.60/1.09  Index Insertion      : 0.00
% 1.60/1.09  Index Deletion       : 0.00
% 1.60/1.09  Index Matching       : 0.00
% 1.60/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
