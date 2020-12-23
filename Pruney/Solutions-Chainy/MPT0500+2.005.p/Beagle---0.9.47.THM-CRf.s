%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:47 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_38,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(c_8,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( k5_relat_1(k6_relat_1(A_5),B_6) = k7_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_1)),A_1) = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [B_7] :
      ( k7_relat_1(B_7,k1_relat_1(B_7)) = B_7
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2])).

tff(c_6,plain,(
    k7_relat_1('#skF_1',k1_relat_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_48,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 21:11:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.10  
% 1.61/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.11  %$ v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1
% 1.61/1.11  
% 1.61/1.11  %Foreground sorts:
% 1.61/1.11  
% 1.61/1.11  
% 1.61/1.11  %Background operators:
% 1.61/1.11  
% 1.61/1.11  
% 1.61/1.11  %Foreground operators:
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.61/1.11  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.61/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.61/1.11  
% 1.61/1.12  tff(f_38, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.61/1.12  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.61/1.12  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 1.61/1.12  tff(c_8, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.61/1.12  tff(c_18, plain, (![A_5, B_6]: (k5_relat_1(k6_relat_1(A_5), B_6)=k7_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.12  tff(c_2, plain, (![A_1]: (k5_relat_1(k6_relat_1(k1_relat_1(A_1)), A_1)=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.12  tff(c_34, plain, (![B_7]: (k7_relat_1(B_7, k1_relat_1(B_7))=B_7 | ~v1_relat_1(B_7) | ~v1_relat_1(B_7))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2])).
% 1.61/1.12  tff(c_6, plain, (k7_relat_1('#skF_1', k1_relat_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.61/1.12  tff(c_40, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_6])).
% 1.61/1.12  tff(c_48, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_40])).
% 1.61/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.12  
% 1.61/1.12  Inference rules
% 1.61/1.12  ----------------------
% 1.61/1.12  #Ref     : 0
% 1.61/1.12  #Sup     : 9
% 1.61/1.12  #Fact    : 0
% 1.61/1.12  #Define  : 0
% 1.61/1.12  #Split   : 0
% 1.61/1.12  #Chain   : 0
% 1.61/1.12  #Close   : 0
% 1.61/1.12  
% 1.61/1.12  Ordering : KBO
% 1.61/1.12  
% 1.61/1.12  Simplification rules
% 1.61/1.12  ----------------------
% 1.61/1.12  #Subsume      : 0
% 1.61/1.12  #Demod        : 1
% 1.61/1.12  #Tautology    : 5
% 1.61/1.12  #SimpNegUnit  : 0
% 1.61/1.12  #BackRed      : 0
% 1.61/1.12  
% 1.61/1.12  #Partial instantiations: 0
% 1.61/1.12  #Strategies tried      : 1
% 1.61/1.12  
% 1.61/1.12  Timing (in seconds)
% 1.61/1.12  ----------------------
% 1.61/1.12  Preprocessing        : 0.28
% 1.61/1.12  Parsing              : 0.16
% 1.61/1.12  CNF conversion       : 0.02
% 1.61/1.12  Main loop            : 0.08
% 1.61/1.12  Inferencing          : 0.04
% 1.61/1.12  Reduction            : 0.02
% 1.61/1.12  Demodulation         : 0.02
% 1.61/1.12  BG Simplification    : 0.01
% 1.61/1.12  Subsumption          : 0.01
% 1.61/1.12  Abstraction          : 0.00
% 1.61/1.12  MUC search           : 0.00
% 1.61/1.12  Cooper               : 0.00
% 1.61/1.12  Total                : 0.39
% 1.61/1.12  Index Insertion      : 0.00
% 1.61/1.12  Index Deletion       : 0.00
% 1.61/1.12  Index Matching       : 0.00
% 1.61/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
