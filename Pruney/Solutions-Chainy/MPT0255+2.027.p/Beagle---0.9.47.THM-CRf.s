%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:42 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   28 (  38 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_131,plain,(
    ! [A_61,B_62] : k3_xboole_0(A_61,k2_xboole_0(A_61,B_62)) = A_61 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k2_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_131])).

tff(c_143,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_140])).

tff(c_162,plain,(
    ! [B_63,C_64] : r1_tarski(k1_tarski(B_63),k2_tarski(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_165,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_162])).

tff(c_180,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k1_xboole_0
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_205,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_165,c_180])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_224,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_12])).

tff(c_44,plain,(
    ! [A_46,B_47] : k2_xboole_0(k1_tarski(A_46),B_47) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_253,plain,(
    ! [B_47] : k2_xboole_0(k1_xboole_0,B_47) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_44])).

tff(c_144,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_46])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.66  
% 2.49/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.67  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.49/1.67  
% 2.49/1.67  %Foreground sorts:
% 2.49/1.67  
% 2.49/1.67  
% 2.49/1.67  %Background operators:
% 2.49/1.67  
% 2.49/1.67  
% 2.49/1.67  %Foreground operators:
% 2.49/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.49/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.67  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.67  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.67  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.49/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.67  
% 2.49/1.68  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.49/1.68  tff(f_79, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.49/1.68  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.49/1.68  tff(f_70, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.49/1.68  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.49/1.68  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.49/1.68  tff(f_75, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.49/1.68  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.49/1.68  tff(c_46, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.68  tff(c_131, plain, (![A_61, B_62]: (k3_xboole_0(A_61, k2_xboole_0(A_61, B_62))=A_61)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.49/1.68  tff(c_140, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k2_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46, c_131])).
% 2.49/1.68  tff(c_143, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_140])).
% 2.49/1.68  tff(c_162, plain, (![B_63, C_64]: (r1_tarski(k1_tarski(B_63), k2_tarski(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.49/1.68  tff(c_165, plain, (r1_tarski(k1_tarski('#skF_1'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_143, c_162])).
% 2.49/1.68  tff(c_180, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k1_xboole_0 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.68  tff(c_205, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_165, c_180])).
% 2.49/1.68  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.68  tff(c_224, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_205, c_12])).
% 2.49/1.68  tff(c_44, plain, (![A_46, B_47]: (k2_xboole_0(k1_tarski(A_46), B_47)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.49/1.68  tff(c_253, plain, (![B_47]: (k2_xboole_0(k1_xboole_0, B_47)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_224, c_44])).
% 2.49/1.68  tff(c_144, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_143, c_46])).
% 2.49/1.68  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_253, c_144])).
% 2.49/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.68  
% 2.49/1.68  Inference rules
% 2.49/1.68  ----------------------
% 2.49/1.68  #Ref     : 0
% 2.49/1.68  #Sup     : 59
% 2.49/1.68  #Fact    : 0
% 2.49/1.68  #Define  : 0
% 2.49/1.68  #Split   : 0
% 2.49/1.68  #Chain   : 0
% 2.49/1.68  #Close   : 0
% 2.49/1.68  
% 2.49/1.68  Ordering : KBO
% 2.49/1.68  
% 2.49/1.68  Simplification rules
% 2.49/1.68  ----------------------
% 2.49/1.68  #Subsume      : 0
% 2.49/1.68  #Demod        : 23
% 2.49/1.68  #Tautology    : 46
% 2.49/1.68  #SimpNegUnit  : 1
% 2.49/1.68  #BackRed      : 4
% 2.49/1.68  
% 2.49/1.68  #Partial instantiations: 0
% 2.49/1.68  #Strategies tried      : 1
% 2.49/1.68  
% 2.49/1.68  Timing (in seconds)
% 2.49/1.68  ----------------------
% 2.49/1.69  Preprocessing        : 0.51
% 2.49/1.69  Parsing              : 0.26
% 2.49/1.69  CNF conversion       : 0.03
% 2.49/1.69  Main loop            : 0.25
% 2.49/1.69  Inferencing          : 0.08
% 2.49/1.69  Reduction            : 0.10
% 2.49/1.69  Demodulation         : 0.08
% 2.49/1.69  BG Simplification    : 0.02
% 2.49/1.69  Subsumption          : 0.04
% 2.49/1.69  Abstraction          : 0.02
% 2.49/1.69  MUC search           : 0.00
% 2.49/1.69  Cooper               : 0.00
% 2.49/1.69  Total                : 0.80
% 2.49/1.69  Index Insertion      : 0.00
% 2.49/1.69  Index Deletion       : 0.00
% 2.49/1.69  Index Matching       : 0.00
% 2.49/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
