%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:34 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_41,negated_conjecture,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(c_8,plain,(
    ! [A_3] : k1_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_7] :
      ( k1_relat_1(A_7) != k1_xboole_0
      | k1_xboole_0 = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_35,plain,(
    ! [A_1] :
      ( k1_relat_1(k6_relat_1(A_1)) != k1_xboole_0
      | k6_relat_1(A_1) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_32])).

tff(c_44,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_35])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/1.05  
% 1.50/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/1.06  %$ v1_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0
% 1.50/1.06  
% 1.50/1.06  %Foreground sorts:
% 1.50/1.06  
% 1.50/1.06  
% 1.50/1.06  %Background operators:
% 1.50/1.06  
% 1.50/1.06  
% 1.50/1.06  %Foreground operators:
% 1.50/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.50/1.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.50/1.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.50/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.50/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.50/1.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.50/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.50/1.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.50/1.06  
% 1.50/1.06  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.50/1.06  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.50/1.06  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 1.50/1.06  tff(f_41, negated_conjecture, ~(k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.50/1.06  tff(c_8, plain, (![A_3]: (k1_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.50/1.06  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.50/1.06  tff(c_32, plain, (![A_7]: (k1_relat_1(A_7)!=k1_xboole_0 | k1_xboole_0=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.50/1.06  tff(c_35, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))!=k1_xboole_0 | k6_relat_1(A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_32])).
% 1.50/1.06  tff(c_44, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_35])).
% 1.50/1.06  tff(c_12, plain, (k6_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.50/1.06  tff(c_47, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 1.50/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/1.06  
% 1.50/1.06  Inference rules
% 1.50/1.06  ----------------------
% 1.50/1.06  #Ref     : 0
% 1.50/1.06  #Sup     : 6
% 1.50/1.06  #Fact    : 0
% 1.50/1.06  #Define  : 0
% 1.50/1.06  #Split   : 0
% 1.50/1.06  #Chain   : 0
% 1.50/1.06  #Close   : 0
% 1.50/1.06  
% 1.50/1.06  Ordering : KBO
% 1.50/1.06  
% 1.50/1.06  Simplification rules
% 1.50/1.06  ----------------------
% 1.50/1.06  #Subsume      : 0
% 1.50/1.06  #Demod        : 3
% 1.50/1.06  #Tautology    : 4
% 1.50/1.06  #SimpNegUnit  : 0
% 1.50/1.06  #BackRed      : 1
% 1.50/1.06  
% 1.50/1.06  #Partial instantiations: 0
% 1.50/1.06  #Strategies tried      : 1
% 1.50/1.06  
% 1.50/1.06  Timing (in seconds)
% 1.50/1.06  ----------------------
% 1.50/1.07  Preprocessing        : 0.24
% 1.50/1.07  Parsing              : 0.13
% 1.50/1.07  CNF conversion       : 0.01
% 1.50/1.07  Main loop            : 0.08
% 1.50/1.07  Inferencing          : 0.04
% 1.50/1.07  Reduction            : 0.02
% 1.50/1.07  Demodulation         : 0.02
% 1.50/1.07  BG Simplification    : 0.01
% 1.50/1.07  Subsumption          : 0.01
% 1.50/1.07  Abstraction          : 0.00
% 1.50/1.07  MUC search           : 0.00
% 1.50/1.07  Cooper               : 0.00
% 1.50/1.07  Total                : 0.34
% 1.50/1.07  Index Insertion      : 0.00
% 1.50/1.07  Index Deletion       : 0.00
% 1.50/1.07  Index Matching       : 0.00
% 1.50/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
