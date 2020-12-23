%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:23 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  48 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_39,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_6,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_34,plain,(
    ! [A_16] :
      ( v1_relat_1(A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_34])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k8_relat_1(A_13,B_14),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_2'(A_22,B_23),A_22)
      | r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [A_22,B_23] :
      ( ~ v1_xboole_0(A_22)
      | r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_52,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,(
    ! [B_28,A_29] :
      ( B_28 = A_29
      | ~ r1_tarski(B_28,A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_50,c_52])).

tff(c_96,plain,(
    ! [A_35,B_36] :
      ( k8_relat_1(A_35,B_36) = B_36
      | ~ v1_xboole_0(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_24,c_65])).

tff(c_98,plain,(
    ! [A_35] :
      ( k8_relat_1(A_35,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_96])).

tff(c_101,plain,(
    ! [A_35] : k8_relat_1(A_35,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_98])).

tff(c_26,plain,(
    k8_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.19  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.85/1.19  
% 1.85/1.19  %Foreground sorts:
% 1.85/1.19  
% 1.85/1.19  
% 1.85/1.19  %Background operators:
% 1.85/1.19  
% 1.85/1.19  
% 1.85/1.19  %Foreground operators:
% 1.85/1.19  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.85/1.19  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.85/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.85/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.85/1.19  
% 1.85/1.20  tff(f_32, axiom, (k1_xboole_0 = o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_xboole_0)).
% 1.85/1.20  tff(f_40, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 1.85/1.20  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.85/1.20  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.85/1.20  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.85/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.85/1.20  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.85/1.20  tff(f_57, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.85/1.20  tff(c_6, plain, (o_0_0_xboole_0=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.20  tff(c_14, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.85/1.20  tff(c_28, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 1.85/1.20  tff(c_34, plain, (![A_16]: (v1_relat_1(A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.85/1.20  tff(c_38, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_34])).
% 1.85/1.20  tff(c_24, plain, (![A_13, B_14]: (r1_tarski(k8_relat_1(A_13, B_14), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.85/1.20  tff(c_46, plain, (![A_22, B_23]: (r2_hidden('#skF_2'(A_22, B_23), A_22) | r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.85/1.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.20  tff(c_50, plain, (![A_22, B_23]: (~v1_xboole_0(A_22) | r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_46, c_2])).
% 1.85/1.20  tff(c_52, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.85/1.20  tff(c_65, plain, (![B_28, A_29]: (B_28=A_29 | ~r1_tarski(B_28, A_29) | ~v1_xboole_0(A_29))), inference(resolution, [status(thm)], [c_50, c_52])).
% 1.85/1.20  tff(c_96, plain, (![A_35, B_36]: (k8_relat_1(A_35, B_36)=B_36 | ~v1_xboole_0(B_36) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_24, c_65])).
% 1.85/1.20  tff(c_98, plain, (![A_35]: (k8_relat_1(A_35, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_96])).
% 1.85/1.20  tff(c_101, plain, (![A_35]: (k8_relat_1(A_35, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_98])).
% 1.85/1.20  tff(c_26, plain, (k8_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.85/1.20  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_26])).
% 1.85/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.20  
% 1.85/1.20  Inference rules
% 1.85/1.20  ----------------------
% 1.85/1.20  #Ref     : 0
% 1.85/1.20  #Sup     : 15
% 1.85/1.20  #Fact    : 0
% 1.85/1.20  #Define  : 0
% 1.85/1.20  #Split   : 0
% 1.85/1.20  #Chain   : 0
% 1.85/1.20  #Close   : 0
% 1.85/1.20  
% 1.85/1.20  Ordering : KBO
% 1.85/1.20  
% 1.85/1.20  Simplification rules
% 1.85/1.20  ----------------------
% 1.85/1.20  #Subsume      : 0
% 1.85/1.20  #Demod        : 6
% 1.85/1.20  #Tautology    : 8
% 1.85/1.20  #SimpNegUnit  : 0
% 1.85/1.20  #BackRed      : 1
% 1.85/1.20  
% 1.85/1.20  #Partial instantiations: 0
% 1.85/1.20  #Strategies tried      : 1
% 1.85/1.20  
% 1.85/1.20  Timing (in seconds)
% 1.85/1.20  ----------------------
% 1.85/1.20  Preprocessing        : 0.28
% 1.85/1.20  Parsing              : 0.15
% 1.85/1.20  CNF conversion       : 0.02
% 1.85/1.20  Main loop            : 0.11
% 1.85/1.20  Inferencing          : 0.05
% 1.85/1.20  Reduction            : 0.03
% 1.85/1.20  Demodulation         : 0.02
% 1.85/1.20  BG Simplification    : 0.01
% 1.85/1.20  Subsumption          : 0.02
% 1.85/1.20  Abstraction          : 0.01
% 1.85/1.20  MUC search           : 0.00
% 1.85/1.20  Cooper               : 0.00
% 1.85/1.20  Total                : 0.41
% 1.85/1.20  Index Insertion      : 0.00
% 1.85/1.21  Index Deletion       : 0.00
% 1.85/1.21  Index Matching       : 0.00
% 1.85/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
