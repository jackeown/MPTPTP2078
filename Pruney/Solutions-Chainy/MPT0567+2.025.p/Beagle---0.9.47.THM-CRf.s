%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:18 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  46 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_xboole_0 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_34,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_2'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_3'(A_13,B_14,C_15),k2_relat_1(C_15))
      | ~ r2_hidden(A_13,k10_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_207,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden('#skF_3'(A_51,B_52,C_53),B_52)
      | ~ r2_hidden(A_51,k10_relat_1(C_53,B_52))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_102,plain,(
    ! [A_38,C_39,B_40] :
      ( ~ r2_hidden(A_38,C_39)
      | ~ r2_hidden(A_38,B_40)
      | ~ r2_hidden(A_38,k5_xboole_0(B_40,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_120,plain,(
    ! [A_38,A_12] :
      ( ~ r2_hidden(A_38,k1_xboole_0)
      | ~ r2_hidden(A_38,A_12)
      | ~ r2_hidden(A_38,A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_102])).

tff(c_327,plain,(
    ! [A_71,C_72,A_73] :
      ( ~ r2_hidden('#skF_3'(A_71,k1_xboole_0,C_72),A_73)
      | ~ r2_hidden(A_71,k10_relat_1(C_72,k1_xboole_0))
      | ~ v1_relat_1(C_72) ) ),
    inference(resolution,[status(thm)],[c_207,c_120])).

tff(c_374,plain,(
    ! [A_77,C_78] :
      ( ~ r2_hidden(A_77,k10_relat_1(C_78,k1_xboole_0))
      | ~ v1_relat_1(C_78) ) ),
    inference(resolution,[status(thm)],[c_32,c_327])).

tff(c_405,plain,(
    ! [C_79] :
      ( ~ v1_relat_1(C_79)
      | k10_relat_1(C_79,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_374])).

tff(c_408,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_405])).

tff(c_412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.28  
% 1.98/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.28  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_xboole_0 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.98/1.28  
% 1.98/1.28  %Foreground sorts:
% 1.98/1.28  
% 1.98/1.28  
% 1.98/1.28  %Background operators:
% 1.98/1.28  
% 1.98/1.28  
% 1.98/1.28  %Foreground operators:
% 1.98/1.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.98/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.98/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.98/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.98/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.98/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.28  
% 2.29/1.29  tff(f_67, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 2.29/1.29  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.29/1.29  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.29/1.29  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.29/1.29  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.29/1.29  tff(c_34, plain, (k10_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.29/1.29  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.29/1.29  tff(c_20, plain, (![A_9]: (r2_hidden('#skF_2'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.29/1.29  tff(c_32, plain, (![A_13, B_14, C_15]: (r2_hidden('#skF_3'(A_13, B_14, C_15), k2_relat_1(C_15)) | ~r2_hidden(A_13, k10_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.29/1.29  tff(c_207, plain, (![A_51, B_52, C_53]: (r2_hidden('#skF_3'(A_51, B_52, C_53), B_52) | ~r2_hidden(A_51, k10_relat_1(C_53, B_52)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.29/1.29  tff(c_24, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.29/1.29  tff(c_102, plain, (![A_38, C_39, B_40]: (~r2_hidden(A_38, C_39) | ~r2_hidden(A_38, B_40) | ~r2_hidden(A_38, k5_xboole_0(B_40, C_39)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.29/1.29  tff(c_120, plain, (![A_38, A_12]: (~r2_hidden(A_38, k1_xboole_0) | ~r2_hidden(A_38, A_12) | ~r2_hidden(A_38, A_12))), inference(superposition, [status(thm), theory('equality')], [c_24, c_102])).
% 2.29/1.29  tff(c_327, plain, (![A_71, C_72, A_73]: (~r2_hidden('#skF_3'(A_71, k1_xboole_0, C_72), A_73) | ~r2_hidden(A_71, k10_relat_1(C_72, k1_xboole_0)) | ~v1_relat_1(C_72))), inference(resolution, [status(thm)], [c_207, c_120])).
% 2.29/1.29  tff(c_374, plain, (![A_77, C_78]: (~r2_hidden(A_77, k10_relat_1(C_78, k1_xboole_0)) | ~v1_relat_1(C_78))), inference(resolution, [status(thm)], [c_32, c_327])).
% 2.29/1.29  tff(c_405, plain, (![C_79]: (~v1_relat_1(C_79) | k10_relat_1(C_79, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_374])).
% 2.29/1.29  tff(c_408, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_405])).
% 2.29/1.29  tff(c_412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_408])).
% 2.29/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.29  
% 2.29/1.29  Inference rules
% 2.29/1.29  ----------------------
% 2.29/1.29  #Ref     : 0
% 2.29/1.29  #Sup     : 80
% 2.29/1.29  #Fact    : 0
% 2.29/1.29  #Define  : 0
% 2.29/1.29  #Split   : 0
% 2.29/1.29  #Chain   : 0
% 2.29/1.29  #Close   : 0
% 2.29/1.29  
% 2.29/1.29  Ordering : KBO
% 2.29/1.29  
% 2.29/1.29  Simplification rules
% 2.29/1.29  ----------------------
% 2.29/1.29  #Subsume      : 20
% 2.29/1.29  #Demod        : 4
% 2.29/1.29  #Tautology    : 19
% 2.29/1.29  #SimpNegUnit  : 1
% 2.29/1.29  #BackRed      : 0
% 2.29/1.29  
% 2.29/1.29  #Partial instantiations: 0
% 2.29/1.29  #Strategies tried      : 1
% 2.29/1.29  
% 2.29/1.29  Timing (in seconds)
% 2.29/1.29  ----------------------
% 2.29/1.29  Preprocessing        : 0.28
% 2.29/1.29  Parsing              : 0.16
% 2.29/1.29  CNF conversion       : 0.02
% 2.29/1.29  Main loop            : 0.25
% 2.29/1.29  Inferencing          : 0.10
% 2.29/1.29  Reduction            : 0.06
% 2.29/1.29  Demodulation         : 0.04
% 2.29/1.29  BG Simplification    : 0.01
% 2.29/1.29  Subsumption          : 0.06
% 2.29/1.29  Abstraction          : 0.01
% 2.29/1.29  MUC search           : 0.00
% 2.29/1.29  Cooper               : 0.00
% 2.29/1.29  Total                : 0.55
% 2.29/1.29  Index Insertion      : 0.00
% 2.29/1.29  Index Deletion       : 0.00
% 2.29/1.29  Index Matching       : 0.00
% 2.29/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
