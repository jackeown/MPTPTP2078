%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:57 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_12,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,(
    ! [B_12,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_13)),A_13)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [B_12] :
      ( k1_relat_1(k7_relat_1(B_12,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_37,c_2])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k7_relat_1(A_2,B_3))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_17,plain,(
    ! [A_10] :
      ( k1_relat_1(A_10) != k1_xboole_0
      | k1_xboole_0 = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    ! [A_16,B_17] :
      ( k1_relat_1(k7_relat_1(A_16,B_17)) != k1_xboole_0
      | k7_relat_1(A_16,B_17) = k1_xboole_0
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_4,c_17])).

tff(c_77,plain,(
    ! [B_18] :
      ( k7_relat_1(B_18,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_72])).

tff(c_83,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.10  
% 1.65/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.10  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.65/1.10  
% 1.65/1.10  %Foreground sorts:
% 1.65/1.10  
% 1.65/1.10  
% 1.65/1.10  %Background operators:
% 1.65/1.10  
% 1.65/1.10  
% 1.65/1.10  %Foreground operators:
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.10  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.65/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.10  
% 1.65/1.11  tff(f_50, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 1.65/1.11  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.65/1.11  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.65/1.11  tff(f_33, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.65/1.11  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.65/1.11  tff(c_12, plain, (k7_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.65/1.11  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.65/1.11  tff(c_37, plain, (![B_12, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_13)), A_13) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.11  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.11  tff(c_42, plain, (![B_12]: (k1_relat_1(k7_relat_1(B_12, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_37, c_2])).
% 1.65/1.11  tff(c_4, plain, (![A_2, B_3]: (v1_relat_1(k7_relat_1(A_2, B_3)) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.11  tff(c_17, plain, (![A_10]: (k1_relat_1(A_10)!=k1_xboole_0 | k1_xboole_0=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.11  tff(c_72, plain, (![A_16, B_17]: (k1_relat_1(k7_relat_1(A_16, B_17))!=k1_xboole_0 | k7_relat_1(A_16, B_17)=k1_xboole_0 | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_4, c_17])).
% 1.65/1.11  tff(c_77, plain, (![B_18]: (k7_relat_1(B_18, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_18))), inference(superposition, [status(thm), theory('equality')], [c_42, c_72])).
% 1.65/1.11  tff(c_83, plain, (k7_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_77])).
% 1.65/1.11  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_83])).
% 1.65/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  Inference rules
% 1.65/1.11  ----------------------
% 1.65/1.11  #Ref     : 0
% 1.65/1.11  #Sup     : 14
% 1.65/1.11  #Fact    : 0
% 1.65/1.11  #Define  : 0
% 1.65/1.11  #Split   : 3
% 1.65/1.11  #Chain   : 0
% 1.65/1.11  #Close   : 0
% 1.65/1.11  
% 1.65/1.11  Ordering : KBO
% 1.65/1.11  
% 1.65/1.11  Simplification rules
% 1.65/1.11  ----------------------
% 1.65/1.11  #Subsume      : 0
% 1.65/1.11  #Demod        : 1
% 1.65/1.11  #Tautology    : 3
% 1.65/1.11  #SimpNegUnit  : 1
% 1.65/1.11  #BackRed      : 0
% 1.65/1.11  
% 1.65/1.11  #Partial instantiations: 0
% 1.65/1.11  #Strategies tried      : 1
% 1.65/1.11  
% 1.65/1.11  Timing (in seconds)
% 1.65/1.11  ----------------------
% 1.65/1.11  Preprocessing        : 0.25
% 1.65/1.11  Parsing              : 0.14
% 1.65/1.11  CNF conversion       : 0.01
% 1.65/1.11  Main loop            : 0.11
% 1.65/1.11  Inferencing          : 0.05
% 1.65/1.11  Reduction            : 0.02
% 1.65/1.11  Demodulation         : 0.02
% 1.65/1.11  BG Simplification    : 0.01
% 1.65/1.11  Subsumption          : 0.02
% 1.65/1.11  Abstraction          : 0.00
% 1.65/1.11  MUC search           : 0.00
% 1.65/1.11  Cooper               : 0.00
% 1.65/1.11  Total                : 0.37
% 1.65/1.11  Index Insertion      : 0.00
% 1.65/1.11  Index Deletion       : 0.00
% 1.65/1.11  Index Matching       : 0.00
% 1.65/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
