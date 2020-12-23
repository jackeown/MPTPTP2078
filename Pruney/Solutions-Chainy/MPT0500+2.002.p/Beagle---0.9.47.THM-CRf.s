%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:47 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r3_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_3] : r3_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [B_12,A_13] :
      ( r1_tarski(B_12,A_13)
      | r1_tarski(A_13,B_12)
      | ~ r3_xboole_0(A_13,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_18])).

tff(c_32,plain,(
    ! [B_15,A_16] :
      ( k7_relat_1(B_15,A_16) = B_15
      | ~ r1_tarski(k1_relat_1(B_15),A_16)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38,plain,(
    ! [B_17] :
      ( k7_relat_1(B_17,k1_relat_1(B_17)) = B_17
      | ~ v1_relat_1(B_17) ) ),
    inference(resolution,[status(thm)],[c_30,c_32])).

tff(c_12,plain,(
    k7_relat_1('#skF_1',k1_relat_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_52,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:45:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.07  
% 1.51/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.08  %$ r3_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_1
% 1.51/1.08  
% 1.51/1.08  %Foreground sorts:
% 1.51/1.08  
% 1.51/1.08  
% 1.51/1.08  %Background operators:
% 1.51/1.08  
% 1.51/1.08  
% 1.51/1.08  %Foreground operators:
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.51/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.51/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.51/1.08  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.51/1.08  
% 1.61/1.08  tff(f_44, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.61/1.08  tff(f_33, axiom, (![A, B]: r3_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_xboole_0)).
% 1.61/1.08  tff(f_31, axiom, (![A, B]: (r3_xboole_0(A, B) <=> (r1_tarski(A, B) | r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_xboole_0)).
% 1.61/1.08  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.61/1.08  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.61/1.08  tff(c_8, plain, (![A_3]: (r3_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.08  tff(c_18, plain, (![B_12, A_13]: (r1_tarski(B_12, A_13) | r1_tarski(A_13, B_12) | ~r3_xboole_0(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.08  tff(c_30, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_18])).
% 1.61/1.08  tff(c_32, plain, (![B_15, A_16]: (k7_relat_1(B_15, A_16)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_16) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.61/1.08  tff(c_38, plain, (![B_17]: (k7_relat_1(B_17, k1_relat_1(B_17))=B_17 | ~v1_relat_1(B_17))), inference(resolution, [status(thm)], [c_30, c_32])).
% 1.61/1.08  tff(c_12, plain, (k7_relat_1('#skF_1', k1_relat_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.61/1.08  tff(c_44, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_12])).
% 1.61/1.08  tff(c_52, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_44])).
% 1.61/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.08  
% 1.61/1.08  Inference rules
% 1.61/1.08  ----------------------
% 1.61/1.08  #Ref     : 0
% 1.61/1.08  #Sup     : 7
% 1.61/1.08  #Fact    : 0
% 1.61/1.08  #Define  : 0
% 1.61/1.08  #Split   : 0
% 1.61/1.08  #Chain   : 0
% 1.61/1.08  #Close   : 0
% 1.61/1.08  
% 1.61/1.08  Ordering : KBO
% 1.61/1.08  
% 1.61/1.08  Simplification rules
% 1.61/1.08  ----------------------
% 1.61/1.08  #Subsume      : 0
% 1.61/1.08  #Demod        : 1
% 1.61/1.08  #Tautology    : 3
% 1.61/1.08  #SimpNegUnit  : 0
% 1.61/1.08  #BackRed      : 0
% 1.61/1.08  
% 1.61/1.08  #Partial instantiations: 0
% 1.61/1.08  #Strategies tried      : 1
% 1.61/1.08  
% 1.61/1.08  Timing (in seconds)
% 1.61/1.08  ----------------------
% 1.61/1.09  Preprocessing        : 0.25
% 1.61/1.09  Parsing              : 0.14
% 1.61/1.09  CNF conversion       : 0.01
% 1.61/1.09  Main loop            : 0.08
% 1.61/1.09  Inferencing          : 0.04
% 1.61/1.09  Reduction            : 0.02
% 1.61/1.09  Demodulation         : 0.02
% 1.61/1.09  BG Simplification    : 0.01
% 1.61/1.09  Subsumption          : 0.01
% 1.61/1.09  Abstraction          : 0.00
% 1.61/1.09  MUC search           : 0.00
% 1.61/1.09  Cooper               : 0.00
% 1.61/1.09  Total                : 0.35
% 1.61/1.09  Index Insertion      : 0.00
% 1.61/1.09  Index Deletion       : 0.00
% 1.61/1.09  Index Matching       : 0.00
% 1.61/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
