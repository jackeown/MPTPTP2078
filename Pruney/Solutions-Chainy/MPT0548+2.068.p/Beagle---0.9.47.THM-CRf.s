%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:44 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 (  50 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_67,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_55,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_32])).

tff(c_353,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden(k4_tarski('#skF_3'(A_59,B_60,C_61),A_59),C_61)
      | ~ r2_hidden(A_59,k9_relat_1(C_61,B_60))
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_45,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | ~ r2_hidden(C_25,k3_xboole_0(A_23,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_26,B_27] :
      ( ~ r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_74,plain,(
    ! [A_30] : k3_xboole_0(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_51])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [A_30,C_5] :
      ( ~ r1_xboole_0(A_30,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_4])).

tff(c_84,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_79])).

tff(c_365,plain,(
    ! [A_59,B_60] :
      ( ~ r2_hidden(A_59,k9_relat_1(k1_xboole_0,B_60))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_353,c_84])).

tff(c_376,plain,(
    ! [A_62,B_63] : ~ r2_hidden(A_62,k9_relat_1(k1_xboole_0,B_63)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_365])).

tff(c_404,plain,(
    ! [B_63] : k9_relat_1(k1_xboole_0,B_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_376])).

tff(c_26,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:29:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.24  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.08/1.24  
% 2.08/1.24  %Foreground sorts:
% 2.08/1.24  
% 2.08/1.24  
% 2.08/1.24  %Background operators:
% 2.08/1.24  
% 2.08/1.24  
% 2.08/1.24  %Foreground operators:
% 2.08/1.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.08/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.08/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.08/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.08/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.08/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.24  
% 2.08/1.25  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.08/1.25  tff(f_67, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.08/1.25  tff(f_55, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.08/1.25  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.08/1.25  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.08/1.25  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.08/1.25  tff(f_70, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.08/1.25  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.25  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.08/1.25  tff(c_32, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.08/1.25  tff(c_34, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_32])).
% 2.08/1.25  tff(c_353, plain, (![A_59, B_60, C_61]: (r2_hidden(k4_tarski('#skF_3'(A_59, B_60, C_61), A_59), C_61) | ~r2_hidden(A_59, k9_relat_1(C_61, B_60)) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.25  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.25  tff(c_45, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | ~r2_hidden(C_25, k3_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.25  tff(c_51, plain, (![A_26, B_27]: (~r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_45])).
% 2.08/1.25  tff(c_74, plain, (![A_30]: (k3_xboole_0(A_30, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_51])).
% 2.08/1.25  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.25  tff(c_79, plain, (![A_30, C_5]: (~r1_xboole_0(A_30, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_74, c_4])).
% 2.08/1.25  tff(c_84, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_79])).
% 2.08/1.25  tff(c_365, plain, (![A_59, B_60]: (~r2_hidden(A_59, k9_relat_1(k1_xboole_0, B_60)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_353, c_84])).
% 2.08/1.25  tff(c_376, plain, (![A_62, B_63]: (~r2_hidden(A_62, k9_relat_1(k1_xboole_0, B_63)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_365])).
% 2.08/1.25  tff(c_404, plain, (![B_63]: (k9_relat_1(k1_xboole_0, B_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_376])).
% 2.08/1.25  tff(c_26, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.08/1.25  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_404, c_26])).
% 2.08/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  Inference rules
% 2.08/1.25  ----------------------
% 2.08/1.25  #Ref     : 0
% 2.08/1.25  #Sup     : 83
% 2.08/1.25  #Fact    : 0
% 2.08/1.25  #Define  : 0
% 2.08/1.25  #Split   : 0
% 2.08/1.25  #Chain   : 0
% 2.08/1.25  #Close   : 0
% 2.08/1.25  
% 2.08/1.25  Ordering : KBO
% 2.08/1.25  
% 2.08/1.25  Simplification rules
% 2.08/1.25  ----------------------
% 2.08/1.25  #Subsume      : 15
% 2.08/1.25  #Demod        : 43
% 2.08/1.25  #Tautology    : 41
% 2.08/1.25  #SimpNegUnit  : 1
% 2.08/1.25  #BackRed      : 2
% 2.08/1.25  
% 2.08/1.25  #Partial instantiations: 0
% 2.08/1.25  #Strategies tried      : 1
% 2.08/1.25  
% 2.08/1.25  Timing (in seconds)
% 2.08/1.25  ----------------------
% 2.08/1.25  Preprocessing        : 0.28
% 2.08/1.25  Parsing              : 0.16
% 2.08/1.25  CNF conversion       : 0.02
% 2.08/1.25  Main loop            : 0.21
% 2.08/1.25  Inferencing          : 0.09
% 2.08/1.25  Reduction            : 0.06
% 2.08/1.25  Demodulation         : 0.04
% 2.08/1.25  BG Simplification    : 0.01
% 2.08/1.25  Subsumption          : 0.03
% 2.08/1.25  Abstraction          : 0.01
% 2.08/1.25  MUC search           : 0.00
% 2.08/1.25  Cooper               : 0.00
% 2.08/1.25  Total                : 0.51
% 2.08/1.25  Index Insertion      : 0.00
% 2.08/1.25  Index Deletion       : 0.00
% 2.08/1.25  Index Matching       : 0.00
% 2.08/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
