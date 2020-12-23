%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:23 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  48 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_40,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_6,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_31,plain,(
    ! [A_14] :
      ( v1_relat_1(A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_35,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_25,c_31])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k8_relat_1(A_11,B_12),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    ! [A_26,B_27] :
      ( r2_xboole_0(A_26,B_27)
      | B_27 = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_2'(A_22,B_23),B_23)
      | ~ r2_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [B_23,A_22] :
      ( ~ v1_xboole_0(B_23)
      | ~ r2_xboole_0(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_65,plain,(
    ! [B_28,A_29] :
      ( ~ v1_xboole_0(B_28)
      | B_28 = A_29
      | ~ r1_tarski(A_29,B_28) ) ),
    inference(resolution,[status(thm)],[c_50,c_48])).

tff(c_76,plain,(
    ! [B_32,A_33] :
      ( ~ v1_xboole_0(B_32)
      | k8_relat_1(A_33,B_32) = B_32
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_22,c_65])).

tff(c_78,plain,(
    ! [A_33] :
      ( k8_relat_1(A_33,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_25,c_76])).

tff(c_81,plain,(
    ! [A_33] : k8_relat_1(A_33,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_78])).

tff(c_24,plain,(
    k8_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:59:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.66/1.16  
% 1.66/1.16  %Foreground sorts:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Background operators:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Foreground operators:
% 1.66/1.16  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.66/1.16  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.66/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.16  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.66/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.66/1.16  
% 1.83/1.17  tff(f_32, axiom, (k1_xboole_0 = o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_xboole_0)).
% 1.83/1.17  tff(f_40, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 1.83/1.17  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.83/1.17  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.83/1.17  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.83/1.17  tff(f_50, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 1.83/1.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.83/1.17  tff(f_61, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.83/1.17  tff(c_6, plain, (o_0_0_xboole_0=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.17  tff(c_14, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.17  tff(c_25, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 1.83/1.17  tff(c_31, plain, (![A_14]: (v1_relat_1(A_14) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.83/1.17  tff(c_35, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_25, c_31])).
% 1.83/1.17  tff(c_22, plain, (![A_11, B_12]: (r1_tarski(k8_relat_1(A_11, B_12), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.83/1.17  tff(c_50, plain, (![A_26, B_27]: (r2_xboole_0(A_26, B_27) | B_27=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.83/1.17  tff(c_44, plain, (![A_22, B_23]: (r2_hidden('#skF_2'(A_22, B_23), B_23) | ~r2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.83/1.17  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.17  tff(c_48, plain, (![B_23, A_22]: (~v1_xboole_0(B_23) | ~r2_xboole_0(A_22, B_23))), inference(resolution, [status(thm)], [c_44, c_2])).
% 1.83/1.17  tff(c_65, plain, (![B_28, A_29]: (~v1_xboole_0(B_28) | B_28=A_29 | ~r1_tarski(A_29, B_28))), inference(resolution, [status(thm)], [c_50, c_48])).
% 1.83/1.17  tff(c_76, plain, (![B_32, A_33]: (~v1_xboole_0(B_32) | k8_relat_1(A_33, B_32)=B_32 | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_22, c_65])).
% 1.83/1.17  tff(c_78, plain, (![A_33]: (k8_relat_1(A_33, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_25, c_76])).
% 1.83/1.17  tff(c_81, plain, (![A_33]: (k8_relat_1(A_33, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_35, c_78])).
% 1.83/1.17  tff(c_24, plain, (k8_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.17  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_24])).
% 1.83/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  Inference rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Ref     : 0
% 1.83/1.17  #Sup     : 11
% 1.83/1.17  #Fact    : 0
% 1.83/1.17  #Define  : 0
% 1.83/1.17  #Split   : 0
% 1.83/1.17  #Chain   : 0
% 1.83/1.17  #Close   : 0
% 1.83/1.17  
% 1.83/1.17  Ordering : KBO
% 1.83/1.17  
% 1.83/1.17  Simplification rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Subsume      : 1
% 1.83/1.17  #Demod        : 3
% 1.83/1.17  #Tautology    : 5
% 1.83/1.17  #SimpNegUnit  : 0
% 1.83/1.17  #BackRed      : 1
% 1.83/1.17  
% 1.83/1.17  #Partial instantiations: 0
% 1.83/1.17  #Strategies tried      : 1
% 1.83/1.17  
% 1.83/1.17  Timing (in seconds)
% 1.83/1.17  ----------------------
% 1.83/1.17  Preprocessing        : 0.26
% 1.83/1.17  Parsing              : 0.14
% 1.83/1.17  CNF conversion       : 0.02
% 1.83/1.17  Main loop            : 0.10
% 1.83/1.17  Inferencing          : 0.04
% 1.83/1.17  Reduction            : 0.03
% 1.83/1.17  Demodulation         : 0.02
% 1.83/1.17  BG Simplification    : 0.01
% 1.83/1.17  Subsumption          : 0.01
% 1.83/1.17  Abstraction          : 0.01
% 1.83/1.17  MUC search           : 0.00
% 1.83/1.17  Cooper               : 0.00
% 1.83/1.17  Total                : 0.39
% 1.83/1.17  Index Insertion      : 0.00
% 1.83/1.17  Index Deletion       : 0.00
% 1.83/1.17  Index Matching       : 0.00
% 1.83/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
