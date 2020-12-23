%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:25 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_47,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_54,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_44])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ! [B_30,A_31] :
      ( r1_tarski(k10_relat_1(B_30,A_31),k1_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_95,plain,(
    ! [A_31] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_31),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_87])).

tff(c_100,plain,(
    ! [A_32] : r1_tarski(k10_relat_1(k1_xboole_0,A_32),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_95])).

tff(c_54,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_2'(A_20,B_21),A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_20,B_21] :
      ( ~ v1_xboole_0(A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_67,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    ! [B_21,A_20] :
      ( B_21 = A_20
      | ~ r1_tarski(B_21,A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_58,c_67])).

tff(c_103,plain,(
    ! [A_32] :
      ( k10_relat_1(k1_xboole_0,A_32) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_100,c_72])).

tff(c_108,plain,(
    ! [A_32] : k10_relat_1(k1_xboole_0,A_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_103])).

tff(c_30,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.17  
% 1.65/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.18  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.65/1.18  
% 1.65/1.18  %Foreground sorts:
% 1.65/1.18  
% 1.65/1.18  
% 1.65/1.18  %Background operators:
% 1.65/1.18  
% 1.65/1.18  
% 1.65/1.18  %Foreground operators:
% 1.65/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.65/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.65/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.65/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.65/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.65/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.18  
% 1.88/1.19  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.88/1.19  tff(f_55, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.88/1.19  tff(f_47, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.88/1.19  tff(f_54, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.88/1.19  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.88/1.19  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.88/1.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.88/1.19  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.88/1.19  tff(f_58, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.88/1.19  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.19  tff(c_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.88/1.19  tff(c_44, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.19  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_44])).
% 1.88/1.19  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.19  tff(c_87, plain, (![B_30, A_31]: (r1_tarski(k10_relat_1(B_30, A_31), k1_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.19  tff(c_95, plain, (![A_31]: (r1_tarski(k10_relat_1(k1_xboole_0, A_31), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_87])).
% 1.88/1.19  tff(c_100, plain, (![A_32]: (r1_tarski(k10_relat_1(k1_xboole_0, A_32), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_95])).
% 1.88/1.19  tff(c_54, plain, (![A_20, B_21]: (r2_hidden('#skF_2'(A_20, B_21), A_20) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.88/1.19  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.19  tff(c_58, plain, (![A_20, B_21]: (~v1_xboole_0(A_20) | r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_54, c_2])).
% 1.88/1.19  tff(c_67, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.19  tff(c_72, plain, (![B_21, A_20]: (B_21=A_20 | ~r1_tarski(B_21, A_20) | ~v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_58, c_67])).
% 1.88/1.19  tff(c_103, plain, (![A_32]: (k10_relat_1(k1_xboole_0, A_32)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_100, c_72])).
% 1.88/1.19  tff(c_108, plain, (![A_32]: (k10_relat_1(k1_xboole_0, A_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_103])).
% 1.88/1.19  tff(c_30, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.88/1.19  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_30])).
% 1.88/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  Inference rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Ref     : 0
% 1.88/1.19  #Sup     : 19
% 1.88/1.19  #Fact    : 0
% 1.88/1.19  #Define  : 0
% 1.88/1.19  #Split   : 0
% 1.88/1.19  #Chain   : 0
% 1.88/1.19  #Close   : 0
% 1.88/1.19  
% 1.88/1.19  Ordering : KBO
% 1.88/1.19  
% 1.88/1.19  Simplification rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Subsume      : 0
% 1.88/1.19  #Demod        : 8
% 1.88/1.19  #Tautology    : 12
% 1.88/1.19  #SimpNegUnit  : 0
% 1.88/1.19  #BackRed      : 2
% 1.88/1.19  
% 1.88/1.19  #Partial instantiations: 0
% 1.88/1.19  #Strategies tried      : 1
% 1.88/1.19  
% 1.88/1.19  Timing (in seconds)
% 1.88/1.19  ----------------------
% 1.88/1.19  Preprocessing        : 0.28
% 1.88/1.19  Parsing              : 0.16
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.12
% 1.88/1.19  Inferencing          : 0.05
% 1.88/1.19  Reduction            : 0.03
% 1.88/1.19  Demodulation         : 0.03
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.02
% 1.88/1.19  Abstraction          : 0.00
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.42
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
