%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:30 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  51 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,k3_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,(
    ! [A_8,C_43] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_43,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_38])).

tff(c_54,plain,(
    ! [C_44] : ~ r2_hidden(C_44,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_49])).

tff(c_63,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_54])).

tff(c_261,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden(k4_tarski(A_76,'#skF_6'(A_76,B_77,C_78)),C_78)
      | ~ r2_hidden(A_76,k10_relat_1(C_78,B_77))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_53,plain,(
    ! [C_43] : ~ r2_hidden(C_43,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_49])).

tff(c_273,plain,(
    ! [A_76,B_77] :
      ( ~ r2_hidden(A_76,k10_relat_1(k1_xboole_0,B_77))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_261,c_53])).

tff(c_284,plain,(
    ! [A_79,B_80] : ~ r2_hidden(A_79,k10_relat_1(k1_xboole_0,B_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_273])).

tff(c_306,plain,(
    ! [B_80] : k10_relat_1(k1_xboole_0,B_80) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_284])).

tff(c_26,plain,(
    k10_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:46:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.22  
% 2.05/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.22  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.05/1.22  
% 2.05/1.22  %Foreground sorts:
% 2.05/1.22  
% 2.05/1.22  
% 2.05/1.22  %Background operators:
% 2.05/1.22  
% 2.05/1.22  
% 2.05/1.22  %Foreground operators:
% 2.05/1.22  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.05/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.22  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.05/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.05/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.22  tff('#skF_7', type, '#skF_7': $i).
% 2.05/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.05/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.05/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.05/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.22  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.05/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.05/1.22  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.05/1.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.05/1.22  
% 2.08/1.23  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.08/1.23  tff(f_61, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.08/1.23  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.08/1.23  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.08/1.23  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.08/1.23  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.08/1.23  tff(f_75, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.08/1.23  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.23  tff(c_16, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.23  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.23  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.08/1.23  tff(c_38, plain, (![A_41, B_42, C_43]: (~r1_xboole_0(A_41, B_42) | ~r2_hidden(C_43, k3_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.23  tff(c_49, plain, (![A_8, C_43]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_38])).
% 2.08/1.23  tff(c_54, plain, (![C_44]: (~r2_hidden(C_44, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_49])).
% 2.08/1.23  tff(c_63, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_54])).
% 2.08/1.23  tff(c_261, plain, (![A_76, B_77, C_78]: (r2_hidden(k4_tarski(A_76, '#skF_6'(A_76, B_77, C_78)), C_78) | ~r2_hidden(A_76, k10_relat_1(C_78, B_77)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.08/1.23  tff(c_53, plain, (![C_43]: (~r2_hidden(C_43, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_49])).
% 2.08/1.23  tff(c_273, plain, (![A_76, B_77]: (~r2_hidden(A_76, k10_relat_1(k1_xboole_0, B_77)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_261, c_53])).
% 2.08/1.23  tff(c_284, plain, (![A_79, B_80]: (~r2_hidden(A_79, k10_relat_1(k1_xboole_0, B_80)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_273])).
% 2.08/1.23  tff(c_306, plain, (![B_80]: (k10_relat_1(k1_xboole_0, B_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_284])).
% 2.08/1.23  tff(c_26, plain, (k10_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.08/1.23  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_306, c_26])).
% 2.08/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  Inference rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Ref     : 1
% 2.08/1.23  #Sup     : 61
% 2.08/1.23  #Fact    : 0
% 2.08/1.23  #Define  : 0
% 2.08/1.23  #Split   : 0
% 2.08/1.23  #Chain   : 0
% 2.08/1.23  #Close   : 0
% 2.08/1.23  
% 2.08/1.23  Ordering : KBO
% 2.08/1.23  
% 2.08/1.23  Simplification rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Subsume      : 11
% 2.08/1.23  #Demod        : 26
% 2.08/1.23  #Tautology    : 27
% 2.08/1.23  #SimpNegUnit  : 1
% 2.08/1.23  #BackRed      : 3
% 2.08/1.23  
% 2.08/1.23  #Partial instantiations: 0
% 2.08/1.23  #Strategies tried      : 1
% 2.08/1.23  
% 2.08/1.23  Timing (in seconds)
% 2.08/1.23  ----------------------
% 2.08/1.23  Preprocessing        : 0.27
% 2.08/1.23  Parsing              : 0.15
% 2.08/1.23  CNF conversion       : 0.02
% 2.08/1.23  Main loop            : 0.19
% 2.08/1.23  Inferencing          : 0.09
% 2.08/1.23  Reduction            : 0.05
% 2.08/1.23  Demodulation         : 0.03
% 2.08/1.23  BG Simplification    : 0.01
% 2.08/1.23  Subsumption          : 0.04
% 2.08/1.23  Abstraction          : 0.01
% 2.08/1.23  MUC search           : 0.00
% 2.08/1.23  Cooper               : 0.00
% 2.08/1.23  Total                : 0.49
% 2.08/1.23  Index Insertion      : 0.00
% 2.08/1.23  Index Deletion       : 0.00
% 2.08/1.23  Index Matching       : 0.00
% 2.08/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
